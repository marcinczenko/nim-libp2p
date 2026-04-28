# SPDX-License-Identifier: Apache-2.0 OR MIT
# Copyright (c) Status Research & Development GmbH

## LIONESS wide-block cipher (Anderson & Biham, 1996), instantiated with
## ChaCha20 (stream cipher), keyed Blake2b-256 (hash), and SHAKE128 (KDF).
##
## The block ``B = L || R`` is split into a 32-byte left half and a right half
## of size ``len(B) - 32``, then four Feistel rounds are applied:
##
##   round 1:  R := R XOR ChaCha20(key = L XOR K1)
##   round 2:  L := L XOR Blake2b_K2(R)
##   round 3:  R := R XOR ChaCha20(key = L XOR K3)
##   round 4:  L := L XOR Blake2b_K4(R)
##
## ``K1..K4`` are derived from a 32-byte master key by feeding it into SHAKE128
## and reading 192 bytes (= 32 + 64 + 32 + 64) of output. See
## ``tests/libp2p/mix/test_lioness.nim`` for vectors.
##
## LIONESS itself does not provide integrity. The Sphinx construction prepends
## ``k`` zero bytes to the plaintext before encryption and verifies them at the
## destination after decryption: tampering anywhere in the ciphertext scrambles
## the entire plaintext through the wide-block PRP, so the leading zeros are
## destroyed with overwhelming probability. See the migration design note for
## details.

{.push raises: [].}

import results
import nimcrypto/[blake2, keccak, utils]
import bearssl/abi/bearssl_block

const
  LionessLeftLen* = 32
    ## Size of the left half ``L``. Must equal both the stream cipher key size
    ## and the hash output size, since L is XORed with each.
  LionessHashKeyLen* = 64
    ## Blake2b MAC key size used in the hash rounds. 64 is Blake2b's maximum
    ## key length without internal truncation (RFC 7693), giving the highest
    ## security margin available without spec deviation. Unlike the stream
    ## cipher key, this size is not constrained by ``LionessLeftLen``: the
    ## hash key is absorbed into Blake2b's state, never XORed with ``L``.
  LionessMasterKeyLen* = 32
    ## Size of the per-hop shared-secret master key from which round keys are
    ## derived.
  LionessMinBlockLen* = LionessLeftLen + 1
    ## Minimum supported block size: at least one byte of right-half data.

  KeyMaterialLen = 2 * LionessLeftLen + 2 * LionessHashKeyLen # 192

  ChaCha20Iv*: array[12, byte] =
    [byte 0x63, 0x68, 0x61, 0x63, 0x68, 0x61, 0x32, 0x30, 0x5f, 0x69, 0x76, 0x00]
    ## Fixed nonce ("chacha20_iv\0"). The per-round key changes each round, so
    ## reusing the IV is safe here. Exported for test reuse.

type
  LionessError* {.pure.} = enum
    BlockTooSmall

  RoundKeys = object
    k1: array[LionessLeftLen, byte]
    k2: array[LionessHashKeyLen, byte]
    k3: array[LionessLeftLen, byte]
    k4: array[LionessHashKeyLen, byte]

  Lioness* = object
    ## Stateless LIONESS instance. Construct via ``Lioness.init(masterKey)`` and
    ## call ``clear`` when no longer needed to wipe round keys from memory.
    keys: RoundKeys

func clear(self: var RoundKeys) =
  burnMem(self.k1)
  burnMem(self.k2)
  burnMem(self.k3)
  burnMem(self.k4)

func clear*(self: var Lioness) =
  ## Zeroize the derived round keys.
  self.keys.clear()

proc deriveRoundKeys(masterKey: openArray[byte]): RoundKeys =
  doAssert masterKey.len == LionessMasterKeyLen, "master key must be 32 bytes"

  var
    ctx: shake128
    material: array[KeyMaterialLen, byte]
  ctx.init()
  ctx.update(masterKey)
  ctx.xof()
  discard ctx.output(addr material[0], uint(KeyMaterialLen))
  ctx.clear()

  var keys: RoundKeys
  copyMem(addr keys.k1[0], addr material[0], LionessLeftLen)
  copyMem(addr keys.k2[0], addr material[LionessLeftLen], LionessHashKeyLen)
  copyMem(
    addr keys.k3[0], addr material[LionessLeftLen + LionessHashKeyLen], LionessLeftLen
  )
  copyMem(
    addr keys.k4[0],
    addr material[2 * LionessLeftLen + LionessHashKeyLen],
    LionessHashKeyLen,
  )
  burnMem(material)
  keys

proc init*(T: type Lioness, masterKey: openArray[byte]): T =
  ## Build a LIONESS instance from a 32-byte master key.
  doAssert masterKey.len == LionessMasterKeyLen, "master key must be 32 bytes"
  T(keys: deriveRoundKeys(masterKey))

# ---------------------------------------------------------------------------
# Round helpers — operate on the whole block in place; the split point is
# always ``LionessLeftLen``.
# ---------------------------------------------------------------------------

proc streamRound(blk: var openArray[byte], subkey: openArray[byte]) =
  ## ``R ^= ChaCha20(key = L XOR subkey, iv = ChaCha20Iv, counter = 0)``
  doAssert subkey.len == LionessLeftLen
  doAssert blk.len > LionessLeftLen

  var roundKey: array[LionessLeftLen, byte]
  for i in 0 ..< LionessLeftLen:
    roundKey[i] = blk[i] xor subkey[i]

  let rightLen = blk.len - LionessLeftLen
  discard chacha20CtRun(
    addr roundKey[0],
    unsafeAddr ChaCha20Iv[0],
    0'u32,
    addr blk[LionessLeftLen],
    csize_t(rightLen),
  )

  burnMem(roundKey)

proc hashRound(blk: var openArray[byte], subkey: openArray[byte]) =
  ## ``L ^= Blake2b_{subkey}(R)``  (32-byte digest)
  doAssert subkey.len == LionessHashKeyLen
  doAssert blk.len > LionessLeftLen

  var ctx: Blake2bContext[256]
  ctx.init(subkey)
  ctx.update(blk.toOpenArray(LionessLeftLen, blk.high))
  let digest = ctx.finish()
  ctx.clear()

  for i in 0 ..< LionessLeftLen:
    blk[i] = blk[i] xor digest.data[i]

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

proc encrypt*(self: Lioness, blk: var openArray[byte]): Result[void, LionessError] =
  ## Encrypt one wide block in place.
  if blk.len < LionessMinBlockLen:
    return err(LionessError.BlockTooSmall)

  streamRound(blk, self.keys.k1)
  hashRound(blk, self.keys.k2)
  streamRound(blk, self.keys.k3)
  hashRound(blk, self.keys.k4)
  ok()

proc decrypt*(self: Lioness, blk: var openArray[byte]): Result[void, LionessError] =
  ## Decrypt one wide block in place. The destination hop should additionally
  ## verify the leading-zeros tag with ``hasLeadingZeros`` to detect tampering.
  if blk.len < LionessMinBlockLen:
    return err(LionessError.BlockTooSmall)

  hashRound(blk, self.keys.k4)
  streamRound(blk, self.keys.k3)
  hashRound(blk, self.keys.k2)
  streamRound(blk, self.keys.k1)
  ok()

func hasLeadingZeros*(blk: openArray[byte], k: int): bool =
  ## True iff the first ``k`` bytes of ``blk`` are zero. Used by the destination
  ## hop after decryption to verify the integrity tag prepended by the sender.
  if blk.len < k or k < 0:
    return false
  var acc: byte = 0
  for i in 0 ..< k:
    acc = acc or blk[i]
  acc == 0

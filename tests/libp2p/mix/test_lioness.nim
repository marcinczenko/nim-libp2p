# SPDX-License-Identifier: Apache-2.0 OR MIT
# Copyright (c) Status Research & Development GmbH

{.used.}

import results
import nimcrypto/[blake2, keccak, utils]
import bearssl/[abi/bearssl_block, rand]
import ../../../libp2p/protocols/mix/lioness
import ../../tools/[unittest, crypto]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

func pat(seed: byte, n: int): seq[byte] =
  ## Deterministic byte pattern: ``i * 31 + seed`` mod 256.
  var bytes = newSeq[byte](n)
  for i in 0 ..< n:
    bytes[i] = byte(((uint32(i) * 31'u32 + uint32(seed)) and 0xff'u32))
  bytes

func incrementing32(): array[32, byte] =
  var bytes: array[32, byte]
  for i in 0 ..< 32:
    bytes[i] = byte(i)
  bytes

# ---------------------------------------------------------------------------
# Sub-primitive vectors (lock the underlying libraries to known outputs;
# LIONESS correctness is verified separately below).
# ---------------------------------------------------------------------------

suite "lioness_subprimitive_vectors":
  test "shake128_kdf_192_bytes":
    let masterKey = incrementing32()

    var
      ctx: shake128
      material: array[192, byte]
    ctx.init()
    ctx.update(masterKey)
    ctx.xof()
    discard ctx.output(addr material[0], uint(material.len))
    ctx.clear()

    let expected = fromHex(
      "066a361dc675f856cecdc02b25218a10cec0cecf79859ec0fec3d409e5847a92" &
        "ba9d4e33d16a3a44cc39b1bdd205b41ba54309172b81078a46b4100571f22208" &
        "6fd89eb089deaf90bf6fbc7d22b3457789f97d11218a0edcfe8d1319a3e6b458" &
        "dfc55e49af14d2ea120935e76e56c7cf6b13929967b9df8e62ff11dc05a3fafc" &
        "979714ce921a9f7aabbbca3f2752beb94f3d7e3d55a47194b3d9abba6b4874ac" &
        "af6ae5d7356d654213071de621a38796d611214bb9eb72c2770d5acc76c07eaa"
    )

    check @material == expected

  test "blake2b_keyed_256_patterned":
    var key: array[64, byte]
    for i in 0 ..< 64:
      key[i] = byte(((uint32(i) * 7'u32 + 3'u32) and 0xff'u32))
    let msg = pat(0xAB'u8, 200)

    var ctx: Blake2bContext[256]
    ctx.init(key)
    ctx.update(msg)
    let digest = ctx.finish()
    ctx.clear()

    let expected =
      fromHex("c283b1ea0df21353d4b8e440d74f3aa7015b99b978402f76c237aac92cbc579d")
    check @(digest.data) == expected

  test "blake2b_keyed_256_empty_message":
    var key: array[64, byte]
    for i in 0 ..< 64:
      key[i] = 0x42'u8

    var ctx: Blake2bContext[256]
    ctx.init(key)
    let digest = ctx.finish()
    ctx.clear()

    let expected =
      fromHex("8fb63b4b405bcb3b515866f25f479fa18006f7bdca7b242c66d17e19275f42a9")
    check @(digest.data) == expected

  test "chacha20_keystream_128_bytes":
    var key: array[32, byte]
    for i in 0 ..< 32:
      key[i] = byte(((uint32(i) * 13'u32 + 1'u32) and 0xff'u32))

    var data: array[128, byte] # all zeros -> output is the keystream
    discard chacha20CtRun(
      addr key[0], unsafeAddr ChaCha20Iv[0], 0'u32, addr data[0], csize_t(data.len)
    )

    let expected = fromHex(
      "fd8e4a87e5ffdfd8e95be1c56cd8efaa4e0ad150b04f831052b740b1a3dc4413" &
        "36e6e18043f3356685e9dc85bce88c53cea52e79937ed78853aa9cd5acb574de" &
        "83ab0e5ef4d3ecd249cf6fa762de6f69b2fd7b9e54f4d5e668c5b81b14c98a22" &
        "5cc9e717335ae020b507a1cae83b70702bb9a1e1d484bdca94d03af0b9e6947b"
    )
    check @data == expected

# ---------------------------------------------------------------------------
# End-to-end LIONESS reference vectors. Any mismatch here is a bug —
# investigate before changing the vector.
# ---------------------------------------------------------------------------

suite "lioness_reference_vectors":
  test "encrypt_64_byte_block_constant_84":
    let masterKey = incrementing32()
    var blk = newSeq[byte](64)
    for i in 0 ..< blk.len:
      blk[i] = 0x84'u8

    let cipher = Lioness.init(masterKey)
    cipher.encrypt(blk).expect("encrypt should succeed")

    let expected = fromHex(
      "6ed531f48dd21f7132da05a9df5cf31bfc3942d2ab7023dfc115e2e436781e5b" &
        "bb1cec4bb960064049f922d0ac2779d035cebcb7cb9e701c7d88ebf68fd290e9"
    )
    check blk == expected

  test "encrypt_minimum_33_byte_patterned_block":
    let masterKey = incrementing32()
    var blk = pat(0x11'u8, 33)

    let cipher = Lioness.init(masterKey)
    cipher.encrypt(blk).expect("encrypt should succeed")

    let expected =
      fromHex("408116c318b7fd2cb83879f1207e31efc89231336645324869e63d848492be8087")
    check blk == expected

  test "encrypt_64_byte_block_alternate_master_key":
    var masterKey: array[32, byte]
    for i in 0 ..< masterKey.len:
      masterKey[i] = 0xFE'u8
    var blk = newSeq[byte](64)
    for i in 0 ..< blk.len:
      blk[i] = 0x84'u8

    let cipher = Lioness.init(masterKey)
    cipher.encrypt(blk).expect("encrypt should succeed")

    let expected = fromHex(
      "3d6dc31e662ba23db2125fa62d7ace39260f78b7a7d56b7742d6966ad678fadb" &
        "87d1dd60bd8440411102f4dbda3cc7153efb38575d0b11ea284c8650ac349282"
    )
    check blk == expected

# ---------------------------------------------------------------------------
# Behavioural tests
# ---------------------------------------------------------------------------

suite "lioness_behaviour":
  test "round_trip_recovers_plaintext":
    var masterKey: array[32, byte]
    rng[].generate(masterKey)
    let cipher = Lioness.init(masterKey)

    for size in [33, 64, 128, 1024, 4096]:
      var blk = newSeq[byte](size)
      rng[].generate(blk)
      let original = blk[0 .. blk.high] # explicit slice forces a fresh buffer

      cipher.encrypt(blk).expect("encrypt should succeed")
      check blk != original
      cipher.decrypt(blk).expect("decrypt should succeed")
      check blk == original

  test "blocks_below_min_size_are_rejected":
    let cipher = Lioness.init(incrementing32())
    var tooSmall = newSeq[byte](LionessLeftLen) # exactly L, no R

    check cipher.encrypt(tooSmall).error == LionessError.BlockTooSmall
    check cipher.decrypt(tooSmall).error == LionessError.BlockTooSmall

  test "different_master_keys_produce_different_ciphertexts":
    var key1, key2: array[32, byte]
    for i in 0 ..< 32:
      key1[i] = byte(i)
      key2[i] = byte(i) xor 0xff'u8

    var blk1 = newSeq[byte](256)
    rng[].generate(blk1)
    var blk2 = blk1

    Lioness.init(key1).encrypt(blk1).expect("encrypt should succeed")
    Lioness.init(key2).encrypt(blk2).expect("encrypt should succeed")
    check blk1 != blk2

  test "tampering_detected_by_leading_zeros_check":
    # Sphinx-style: prepend k=16 zero bytes, encrypt, flip a byte deep in the
    # ciphertext (well beyond the first k bytes — the scenario from PR #2233),
    # decrypt, and check the integrity tag.
    const k = 16
    let masterKey = incrementing32()
    let cipher = Lioness.init(masterKey)

    var blk = newSeq[byte](512)
    rng[].generate(blk)
    for i in 0 ..< k:
      blk[i] = 0
    let tagged = blk[0 .. blk.high]

    cipher.encrypt(blk).expect("encrypt should succeed")

    # Round-trip without tampering passes the integrity check.
    var clean = blk[0 .. blk.high]
    cipher.decrypt(clean).expect("decrypt should succeed")
    check hasLeadingZeros(clean, k)
    check clean == tagged

    # Flip a single bit far beyond the leading-zeros window.
    blk[256] = blk[256] xor 0x01'u8
    cipher.decrypt(blk).expect("decrypt should succeed")
    check not hasLeadingZeros(blk, k)

  test "has_leading_zeros_edge_cases":
    var allZero = newSeq[byte](32)
    check hasLeadingZeros(allZero, 16)
    check hasLeadingZeros(allZero, 32)
    check not hasLeadingZeros(allZero, 33) # k > len

    var oneNonZero = newSeq[byte](32)
    oneNonZero[10] = 0x01'u8
    check hasLeadingZeros(oneNonZero, 10)
    check not hasLeadingZeros(oneNonZero, 11)

    check hasLeadingZeros(allZero, 0) # k = 0 trivially holds

#!/usr/bin/env python3

# PREPARATION:
# sudo apt install -y pip
# sudo apt install -y python3.11-venv
# python3 -m venv ./venv
# source ./venv/bin/activate
# pip install base58
# pip install pyaes
# pip install ecdsa
# pip install coincurve
# pip install pycryptodome

import base58
import base64
import hashlib
import hmac
import json
import unicodedata
import pyaes
import string
import zlib

from hashlib import sha256, new
from ecdsa import SigningKey, SECP256k1
from coincurve import PublicKey, PrivateKey
from ecdsa.ellipticcurve import Point
from Crypto.Cipher import AES
from Crypto.Util.Padding import unpad


CURVE_ORDER = 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_BAAEDCE6_AF48A03B_BFD25E8C_D0364141

# Chinese, Japanese, Korean
# http://www.asahi-net.or.jp/~ax2s-kmtn/ref/unicode/e_asia.html
CJK_INTERVALS = [
    (0x4E00,  0x9FFF),   # CJK Unified Ideographs
    (0x3400,  0x4DBF),   # CJK Unified Ideographs Extension A
    (0x20000, 0x2A6DF),  # CJK Unified Ideographs Extension B
    (0x2A700, 0x2B73F),  # CJK Unified Ideographs Extension C
    (0x2B740, 0x2B81F),  # CJK Unified Ideographs Extension D
    (0xF900,  0xFAFF),   # CJK Compatibility Ideographs
    (0x2F800, 0x2FA1D),  # CJK Compatibility Ideographs Supplement
    (0x3190,  0x319F),   # Kanbun
    (0x2E80,  0x2EFF),   # CJK Radicals Supplement
    (0x2F00,  0x2FDF),   # CJK Radicals
    (0x31C0,  0x31EF),   # CJK Strokes
    (0x2FF0,  0x2FFF),   # Ideographic Description Characters
    (0xE0100, 0xE01EF),  # Variation Selectors Supplement
    (0x3100,  0x312F),   # Bopomofo
    (0x31A0,  0x31BF),   # Bopomofo Extended
    (0xFF00,  0xFFEF),   # Halfwidth and Fullwidth Forms
    (0x3040,  0x309F),   # Hiragana
    (0x30A0,  0x30FF),   # Katakana
    (0x31F0,  0x31FF),   # Katakana Phonetic Extensions
    (0x1B000, 0x1B0FF),  # Kana Supplement
    (0xAC00,  0xD7AF),   # Hangul Syllables
    (0x1100,  0x11FF),   # Hangul Jamo
    (0xA960,  0xA97F),   # Hangul Jamo Extended A
    (0xD7B0,  0xD7FF),   # Hangul Jamo Extended B
    (0x3130,  0x318F),   # Hangul Compatibility Jamo
    (0xA4D0,  0xA4FF),   # Lisu
    (0x16F00, 0x16F9F),  # Miao
    (0xA000,  0xA48F),   # Yi Syllables
    (0xA490,  0xA4CF),   # Yi Radicals
]


def convert8to5(data):
    acc = 0
    bits = 0
    ret = []
    mask = (1 << 5) - 1
    for value in data:
        acc = (acc << 8) | value
        bits += 8
        while bits >= 5:
            bits -= 5
            ret.append((acc >> bits) & mask)
    if bits:
        ret.append((acc << (5 - bits)) & mask)
    elif bits >= 8 or ((acc << (5 - bits)) & mask):
        return None
    return ret


def bech32_polymod(values):
    generators = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for v in values:
        b = (chk >> 25)
        chk = (chk & 0x1ffffff) << 5 ^ v
        for i in range(5):
            if (b >> i) & 1:
                chk ^= generators[i]
    return chk


def bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]


def bech32_create_checksum(hrp, data):
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]


def bech32_encode(hrp, data):
    CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
    combined = data + bech32_create_checksum(hrp, data)
    return hrp + "1" + "".join([CHARSET[d] for d in combined])

# Chinese, Japanese, Korean
def is_CJK(c: str) -> bool:
    n = ord(c)
    for imin, imax in CJK_INTERVALS:
        if imin <= n <= imax:
            return True
    return False


def normalize_text(seed: str) -> str:
    # normalize
    seed = unicodedata.normalize("NFKD", seed)
    # lower
    seed = seed.lower()
    # remove accents
    seed = u''.join([c for c in seed if not unicodedata.combining(c)])
    # normalize whitespaces
    seed = u' '.join(seed.split())
    # remove whitespaces between CJK (Chinese, Japanese, Korean)
    seed = u''.join([seed[i] for i in range(len(seed)) if not (seed[i] in string.whitespace and is_CJK(seed[i-1]) and is_CJK(seed[i+1]))])
    return seed


def get_bip32_seed(mnemonic: str, password: str):
    PBKDF2_ROUNDS = 2048
    mnemonic = normalize_text(mnemonic)
    passphrase = normalize_text(password)
    bip32_seed = hashlib.pbkdf2_hmac("sha512", mnemonic.encode("utf-8"), b"electrum" + passphrase.encode("utf-8"), iterations = PBKDF2_ROUNDS)
    return bip32_seed


def get_master_k_c(bip32_seed: bytes):
    I = hmac.digest(b"Bitcoin seed", bip32_seed, hashlib.sha512)
    master_k = I[0:32]
    master_c = I[32:]
    return (master_k, master_c)


def prv_to_pub(prv_key) -> bytes:
    sk = SigningKey.from_string(prv_key, curve=SECP256k1)
    pub_key = sk.get_verifying_key().to_string()
    return pub_key


def pub_compressed(pub_key: bytes):
    prefix = b'\x02' if pub_key[32:][-1] % 2 == 0 else b'\x03'
    return prefix + pub_key[:32]


# Link: https://learnmeabitcoin.com/technical/keys/hd-wallets/extended-keys/
# Extended Private Key (Hardened Child)
def ext_prv_key_hardened_child(prv_key: bytes, chain_code: bytes, index: int):
    index = index + 2147483648
    data = b'\x00' + prv_key + index.to_bytes(4, byteorder="big")
    hmac_sha512 = hmac.new(chain_code, data, hashlib.sha512).digest()
    iprv_key = int.from_bytes(prv_key, byteorder="big")
    ihmac_sha512 = int.from_bytes(hmac_sha512[:32], byteorder="big")
    child_prv_key = ((iprv_key + ihmac_sha512) % CURVE_ORDER).to_bytes(32, byteorder="big")
    child_chain_code = hmac_sha512[32:]
    return (child_prv_key, child_chain_code)


# Link: https://learnmeabitcoin.com/technical/keys/hd-wallets/extended-keys/
# Extended Private Key (Normal Child)
def ex_prv_key_normal_child(prv_key: bytes, chain_code: bytes, index: int):
    assert index < 2147483648
    public_key = prv_to_pub(prv_key)
    data = pub_compressed(public_key) + index.to_bytes(4, byteorder="big")
    hmac_sha512 = hmac.new(chain_code, data, hashlib.sha512).digest()
    iprv_key = int.from_bytes(prv_key, byteorder="big")
    ihmac_sha512 = int.from_bytes(hmac_sha512[:32], byteorder="big")
    child_prv_key = ((iprv_key + ihmac_sha512) % CURVE_ORDER).to_bytes(32, byteorder="big")
    child_chain_code = hmac_sha512[32:]
    return (child_prv_key, child_chain_code)


# Link: https://learnmeabitcoin.com/technical/keys/hd-wallets/extended-keys/
# Extended Public Key (Normal Child)
def ext_pub_normal_child(pub_key: bytes, chain_code: bytes, index: int):
    assert index < 2147483648
    data = pub_compressed(pub_key) + index.to_bytes(4, byteorder="big")
    hmac_sha512 = hmac.new(chain_code, data, hashlib.sha512).digest()
    pubkey1 = PublicKey(pub_compressed(prv_to_pub(hmac_sha512[:32]))).point()
    pubkey2 = PublicKey(pub_compressed(pub_key)).point()
    point1 = Point(SECP256k1.curve, pubkey1[0] , pubkey1[1])
    point2 = Point(SECP256k1.curve, pubkey2[0] , pubkey2[1])
    sum = point1 + point2
    child_pubkey = PublicKey.from_point(sum.x(), sum.y()).format(False)[1:]
    child_chaincode = hmac_sha512[32:]
    return (child_pubkey, child_chaincode)


def get_bc_address(pub_key: bytes):
    sha = sha256(pub_compressed(pub_key)).digest()
    ripemd = new("ripemd160", sha).digest()
    data = [0] + convert8to5(ripemd)
    return bech32_encode("bc", data)


def get_addresses(prv_key: bytes, chain_code: bytes, index: int, count: int):
    recv_addr = []
    child_prv_key, child_chain_code = ex_prv_key_normal_child(prv_key, chain_code, index)
    child_pub_key = prv_to_pub(child_prv_key)
    for i in range(count):
        pub_key, _ = ext_pub_normal_child(child_pub_key, child_chain_code, i)
        recv_addr.append(get_bc_address(pub_key))
    return recv_addr


class ElectrumWallet:
    def __init__(self, password):
        self.iPassword = password
        self.iWalletData = {}

    def load(self, path:str):
        secret = hashlib.pbkdf2_hmac("sha512", self.iPassword.encode("utf-8"), b"", iterations=1024)
        scalar = int.from_bytes(secret, byteorder="big", signed=False) % CURVE_ORDER
        with open(path, "rb") as file:
            bin_data = file.read().decode("utf-8")
            b64_data = base64.b64decode(bin_data)
            magic = b64_data[0:4]
            if magic == b"BIE1":
                ciphertext = b64_data[37:-32]
                pubkey = PublicKey(b64_data[4:37])
                p1 = Point(SECP256k1.curve, pubkey.point()[0], pubkey.point()[1])
                p2 = p1 * scalar
                ecdh_key = PublicKey.from_point(p2.x(), p2.y()).format(True)
                key = hashlib.sha512(ecdh_key).digest()
                iv, key_e = key[0:16], key[16:32]
                aes_cbc = pyaes.AESModeOfOperationCBC(key_e, iv=iv)
                aes = pyaes.Decrypter(aes_cbc, padding=pyaes.PADDING_NONE)
                data = aes.feed(ciphertext) + aes.feed()
                jdata = zlib.decompress(data)
                self.iWalletData = json.loads(jdata.decode("utf8"))

    def decrypt(self, ciphertext):
        ciphertext = bytes(base64.b64decode(ciphertext, validate=True))
        sha1 = hashlib.sha256(self.iPassword.encode("utf-8")).digest()
        secret = hashlib.sha256(sha1).digest()
        iv, e = ciphertext[:16], ciphertext[16:]
        aes_cbc = pyaes.AESModeOfOperationCBC(secret, iv=iv)
        aes = pyaes.Decrypter(aes_cbc, padding=pyaes.PADDING_NONE)
        data = aes.feed(e) + aes.feed()
        decrypted_data = unpad(data, AES.block_size).decode("utf-8")
        return decrypted_data


    def save(self, path:str):
        with open(path, 'w') as file:
            json.dump(self.iWalletData, file, indent=4)


    def get_seed(self):
        seed = self.iWalletData["keystore"]["seed"]
        return self.decrypt(seed)

    def get_xprv(self):
        xprv = self.iWalletData["keystore"]["xprv"]
        return self.decrypt(xprv)

    def get_xpub(self):
        xpub = self.iWalletData["keystore"]["xpub"]
        return xpub


# Link: https://learnmeabitcoin.com/technical/keys/hd-wallets/extended-keys/
# Serialized Extended Private/Public Key
class XKey:
    def __init__(self, xkey: str):
        self.XKey = xkey
        data = base58.b58decode(xkey)
        self.Version = data[:4]
        self.Depth = int(data[4])
        self.Fingerprint = data[5:9]
        self.ChildNumber = int.from_bytes(data[9:13], byteorder="big")
        self.ChainCode = data[13:45]
        self.Key = data[45:]

    def ver_desc(self):
        v = {
            "0488ade4": "xprv",
            "0488b21e": "xpub",
            "049d7878": "yprv (BIP 49)",
            "049d7cb2": "ypub (BIP 49)",
            "04b2430c": "zprv (BIP 84)",
            "04b24746": "zpub (BIP 84)"
        }
        return v[self.Version.hex()]
    
    def __str__(self):
        data = base58.b58decode(self.XKey)
        s =  f"XKEY: {self.XKey}\n"
        s += f"BIN:  {data.hex()}\n"
        s += f"\tVersion:      {self.Version.hex()} ({self.ver_desc()})\n"
        s += f"\tDepth:        {self.Depth}\n"
        s += f"\tFingerprint:  {self.Fingerprint.hex()}\n"
        s += f"\tChild Number: {self.ChildNumber}\n"
        s += f"\tChain Code:   {self.ChainCode.hex()}\n"
        s += f"\tKey:          ({self.Key[0:1].hex()}) {self.Key[1:].hex()}\n"
        return s


# Link: https://learnmeabitcoin.com/technical/keys/private-key/wif/
# Wallet Import Format
class WIF:
    def __init__(self, wif: str):
        data = base58.b58decode(wif)
        self.Wif = wif
        self.Prefix = data[0:1]
        self.PrvKey = data[1:33]
        self.Compression = data[33:34]
        self.Checksum = data[34:]
    
    def __str__(self):
        return f"WIF[prefix:{self.Prefix.hex()} prvkey:{self.PrvKey.hex()} compression:{self.Compression.hex()} checksum:{self.Checksum.hex()}]"


def main():
    wallet_password = "PUT WALLET'S PASSWORD HERE"
    path_to_encrypted_wallet = "PUT PATH TO WALLET'S FILE HERE"
    path_to_decryted_wallet  = "PUT PATH TO DECRYPTED WALLET'S FILE HERE"
    path_to_export_json = "PUT PATH TO EXPORTED KEYS JSON FILE HERE"


    electrum_wallet = ElectrumWallet(wallet_password)
    electrum_wallet.load(path_to_encrypted_wallet)
    electrum_wallet.save(path_to_decryted_wallet)

    xprv = XKey(electrum_wallet.get_xprv())
    print(xprv)
    print()
    xpub = XKey(electrum_wallet.get_xpub())
    print(xpub)
    print()
    seed = electrum_wallet.get_seed()
    bip32_seed = get_bip32_seed(seed, "")
    master_k, master_c = get_master_k_c(bip32_seed)
    print("SEED:", seed)
    print(f"Master Key:               {master_k.hex()}")
    print(f"Master Chain Code:        {master_c.hex()}")
    harden_child_prv_key, harden_child_chain_code = ext_prv_key_hardened_child(master_k, master_c, 0)
    print(f"Harden Child Private Key: {harden_child_prv_key.hex()}")
    print(f"Harden Child Chain Code:  {harden_child_chain_code.hex()}")
    print()
    print()
    json_export = None
    with open(path_to_export_json, "r") as file:
        json_export = json.load(file)
    print("RECEIVING ADDRESSES:")
    recv_addrs = get_addresses(harden_child_prv_key, harden_child_chain_code, 0, 20)
    for addr in recv_addrs:
        assert addr in json_export.keys()
        p2wpkh = json_export[addr]
        wif = WIF(p2wpkh.split(":")[1])
        assert addr == get_bc_address(prv_to_pub(wif.PrvKey))
        print(f"\t{addr}    {p2wpkh}    {wif}")
    print()
    print("CHANGE ADDRESSES:")
    change_addrs = get_addresses(harden_child_prv_key, harden_child_chain_code, 1, 10)
    for addr in change_addrs:
        assert addr in json_export.keys()
        p2wpkh = json_export[addr]
        wif = WIF(p2wpkh.split(":")[1])
        assert addr == get_bc_address(prv_to_pub(wif.PrvKey))
        print(f"\t{addr}    {p2wpkh}    {wif}")
    return 0


if __name__ == "__main__":
    main()
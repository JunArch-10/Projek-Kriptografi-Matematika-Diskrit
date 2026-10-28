"""
Analisis Kinerja Validasi Kunci Publik Diffie-Hellman:
Simbol Jacobi vs Eksponensiasi Modular, dengan RSA-CRT sebagai pembanding.
Hanya library standar Python (tanpa pip install).
"""
import random, time, statistics, sys

# ---------------------------------------------------------------
# 1. BILANGAN PRIMA
# ---------------------------------------------------------------
SMALL = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

def is_prime(n, k=20):
    """Miller-Rabin. n-1 = 2^s * d, uji k basis acak."""
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for sp in SMALL:
        if n == sp: return True
        if n % sp == 0: return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def gen_prime(bits, mod4=None):
    """Prima acak 'bits' bit. mod4=3 -> paksa p = 3 (mod 4)."""
    while True:
        p = random.getrandbits(bits) | (1 << (bits - 1)) | 1
        if mod4 == 3: p |= 2
        if is_prime(p, 10): return p

def pi_scaled(bits):
    """floor(pi * 2^bits) lewat rumus Machin (aritmetika integer murni)."""
    prec = bits + 64
    one = 1 << prec
    def arctan_inv(x):
        total = term = one // x
        x2, n, sign = x * x, 3, -1
        while term:
            term //= x2
            total += sign * (term // n)
            sign, n = -sign, n + 2
        return total
    pi = 4 * (4 * arctan_inv(5) - arctan_inv(239))
    return pi >> (prec - bits)

# (bit, konstanta k) dari RFC 2409 / RFC 3526
RFC = {768: 149686, 1024: 129093, 1536: 741804, 2048: 124476, 3072: 1690314, 4096: 240904}

def rfc_safe_prime(n):
    """p = 2^n - 2^(n-64) - 1 + 2^64 * ( floor(2^(n-130) * pi) + k )"""
    k = RFC[n]
    return (1 << n) - (1 << (n - 64)) - 1 + (1 << 64) * (pi_scaled(n - 130) + k)

# ---------------------------------------------------------------
# 2. SIMBOL JACOBI (tanpa eksponensiasi)
# ---------------------------------------------------------------
def jacobi_symbol(a, n):
    assert n % 2 == 1 and n > 0
    a %= n
    t = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): t = -t
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: t = -t
        a %= n
    return t if n == 1 else 0

# ---------------------------------------------------------------
# 3. UJI KEBENARAN
# ---------------------------------------------------------------
def check_equivalence(p, trials):
    """Bandingkan Euler (y^((p-1)/2)) dengan Jacobi. Harus 0 ketidakcocokan."""
    e_exp = (p - 1) // 2
    bad = qr = 0
    for _ in range(trials):
        y = random.randrange(2, p - 1)
        e = pow(y, e_exp, p)
        j = jacobi_symbol(y, p)
        if e == 1: qr += 1
        if not ((e == 1 and j == 1) or (e == p - 1 and j == -1)):
            bad += 1
    return bad, qr

# ---------------------------------------------------------------
# 4. BENCHMARK
# ---------------------------------------------------------------
def bench(fn, repeats):
    fn()  # warm-up
    res = []
    for _ in range(repeats):
        t = time.perf_counter_ns()
        fn()
        res.append((time.perf_counter_ns() - t) / 1e6)  # ms total
    return statistics.mean(res), (statistics.stdev(res) if repeats > 1 else 0.0)

def per_op(m, s, n): return m / n, s / n

def dh_case(label, p, bits, trials, repeats):
    e_exp = (p - 1) // 2
    ys = [random.randrange(2, p - 1) for _ in range(trials)]
    a = random.getrandbits(bits - 1) | 1       # eksponen rahasia penuh

    def f_range():
        for y in ys: 1 < y < p - 1
    def f_full():
        for y in ys: pow(y, e_exp, p) == 1
    def f_jac():
        for y in ys: jacobi_symbol(y, p) == 1
    def f_shared():
        for y in ys: pow(y, a, p)

    r = [per_op(*bench(f, repeats), trials) for f in (f_range, f_full, f_jac, f_shared)]
    bad, qr = check_equivalence(p, min(trials, 500))
    return dict(label=label, bits=bits, bad=bad, range=r[0], full=r[1], jac=r[2], shared=r[3])

def rsa_case(bits, trials, repeats):
    """RSA-CRT dekripsi/tanda tangan, modulus n sebesar 'bits' bit."""
    p = gen_prime(bits // 2); q = gen_prime(bits // 2)
    while q == p: q = gen_prime(bits // 2)
    n, e = p * q, 65537
    phi = (p - 1) * (q - 1)
    d = pow(e, -1, phi)
    dp, dq, qinv = d % (p - 1), d % (q - 1), pow(q, -1, p)
    cs = [random.randrange(2, n - 1) for _ in range(trials)]
    def crt():
        for c in cs:
            m1 = pow(c, dp, p); m2 = pow(c, dq, q)
            h = qinv * (m1 - m2) % p
            m2 + h * q
    def plain():
        for c in cs: pow(c, d, n)
    m = cs[0]
    # cek benar
    c0 = pow(m, e, n)
    m1 = pow(c0, dp, p); m2 = pow(c0, dq, q)
    assert (m2 + (qinv * (m1 - m2) % p) * q) == m
    return per_op(*bench(crt, repeats), trials), per_op(*bench(plain, repeats), trials)

def main():
    def arg(name, default):
        for a in sys.argv[1:]:
            if a.startswith(name + "="): return a.split("=", 1)[1]
        return default
    quick = "--quick" in sys.argv
    sizes = [int(x) for x in arg("--sizes", "768,1024,1536,2048,3072,4096" if not quick else "1024,1536,2048").split(",")]
    trials = int(arg("--trials", 20 if quick else 200))
    repeats = int(arg("--repeats", 3 if quick else 5))
    random.seed(2026)

    print("=" * 78)
    print(f" BENCHMARK VALIDASI DH | trials={trials}/run, repeat={repeats}")
    print("=" * 78)
    rows, rsa = [], {}
    for bits in sizes:
        print(f"\n[{bits}-bit] membuat parameter...", flush=True)
        p_safe = rfc_safe_prime(bits)
        assert p_safe.bit_length() == bits
        assert is_prime(p_safe, 5) and is_prime((p_safe - 1) // 2, 5), "bukan safe prime!"
        rows.append(dh_case("Safe prime RFC", p_safe, bits, trials, repeats))
        p_rand = gen_prime(bits, mod4=3)
        rows.append(dh_case("Prima acak (3 mod 4)", p_rand, bits, trials, repeats))
        print(f"[{bits}-bit] RSA-CRT...", flush=True)
        rsa[bits] = rsa_case(bits, trials, repeats)

    print("\n" + "=" * 78)
    print("HASIL DH (ms/operasi, mean ± std)")
    print("=" * 78)
    for r in rows:
        f, j, s = r['full'], r['jac'], r['shared']
        print(f"\n{r['bits']}-bit | {r['label']} | ketidakcocokan Euler-Jacobi: {r['bad']}")
        print(f"  Cek rentang        : {r['range'][0]*1e6:10.1f} ns")
        print(f"  Validasi eksp y^q  : {f[0]:8.3f} ± {f[1]:.3f} ms")
        print(f"  Validasi Jacobi    : {j[0]:8.3f} ± {j[1]:.3f} ms")
        print(f"  Hitung kunci sesi  : {s[0]:8.3f} ± {s[1]:.3f} ms  (eksponen penuh)")
        print(f"  Speedup Jacobi/eksp: {f[0]/j[0]:6.2f}x")
        print(f"  Overhead thd sesi  : eksp +{f[0]/s[0]*100:.1f}% | Jacobi +{j[0]/s[0]*100:.1f}%")
    print("\n" + "=" * 78)
    print("RSA (ms/operasi, operasi kunci privat)")
    print("=" * 78)
    for b, ((cm, cs), (pm, ps)) in rsa.items():
        print(f"{b}-bit | RSA-CRT: {cm:.3f} ± {cs:.3f} | RSA tanpa CRT: {pm:.3f} ± {ps:.3f} | CRT {pm/cm:.2f}x lebih cepat")

if __name__ == "__main__":
    main()

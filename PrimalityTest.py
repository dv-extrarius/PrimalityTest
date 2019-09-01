from __future__ import print_function, division

__all__ = [
    "ModInverse", "gcd", "SplitInt",
    "Jacobi", "IsNonQuadraticResidue", "PrimeModRootFinder", "LehmerSequenceComputer",
    "TestSmallDivisors", "MillerRabinMultiWitnessPrimalityTest", "SelfridgePrimalityTest", "ExtendedLehmerPrimalityTest",
    "IsPrime"
]

def ModInverse(a, n):
    t = 0
    newt = 1
    r = n
    newr = a % n
    while newr != 0:
        quotient = r // newr
        (t, newt) = (newt, t - quotient * newt)
        (r, newr) = (newr, r - quotient * newr)
    if r > 1:
        return None
    if t < 0:
        t = t + n
    return t % n

def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a

def SplitInt(n):
    if n == 0:
        return (0, 0)
    exp = (n & (-n)).bit_length() - 1
    mul = n >> exp
    return (exp, mul)

def Jacobi(m, n):
    #(a*b/n) = (a/n) * (b/n)
    #(m/n) = ((n % m)/m) * (-1)^((n-1)/2*(m-1)/2)
    #(2/n) = (-1)^((n^2 - 1)/8)
    if (n & 1) == 0:
        raise ValueError("n must be odd!")
    J = +1
    m %= n
    while (m > 1) and (n != 1):
        if (m & 1) == 0:
            #This works because n is never even
            temp = (n & 7)
            temp = ((temp * temp - 1) >> 3)
            if (temp & 1):
                J *= -1
            m >>= 1
        else:
            #This works because here n and m are both odd
            temp = (((n & 3) - 1) & ((m & 3) - 1)) >> 1
            if (temp & 1):
                J *= -1
            m, n = (n % m), m
    if (m == 1) or (n == 1):
        return J
    elif (m == 0):
        return 0
    else:
        raise ValueError("Unexpected")

def IsNonQuadraticResidue(a, p):
    return (gcd(a, p) == 1) and (Jacobi(a, p) == -1) and (pow(a, (p - 1) // 2, p) == p-1)

class PrimeModRootFinder(object):
    __slots__ = ("_n", "_e", "_s", "_g")
    def __init__(self, n):
        self._n = n
        self._e, self._s = SplitInt(n - 1)

        for non in range(2, n):
            if IsNonQuadraticResidue(non, n):
                break
        else:
            raise ValueError("Cannot find non-residue mod n!")
        self._g = pow(non, self._s, n)

    @property
    def mod(self):
        return self._n

    def root(self, a):
        if a == 0:
            return (0, 0)
        n = self._n
        a %= n
        if Jacobi(a, n) == -1:
            return (None, None)

        if a == 1:
            return (1, n-1)

        x = pow(a, (self._s+1)//2, n)
        b = pow(a, self._s, n)
        g = self._g
        r = self._e

        while 1:
            bm = b
            for m in range(0, r):
                if bm == 1:
                    break
                bm = (bm * bm) % n
            else:
                return (None, None)
            if m == 0:
                return (x, (-x)%n)

            t = pow(g, 1 << (r - m - 1), n)
            x = (x * t) % n
            b = (b * t * t) % n
            g = (t * t) % n
            r = m

    def roots(self, a):
        return self.root(a)


# U[n](R, Q) := (R - 2 * Q) * U[n-2](R, Q) - Q^2 * U[n-4](R, Q);
# U[0](R, Q) := 0;
# U[1](R, Q) := 1;
# U[2](R, Q) := 1;
# U[3](R, Q) := R - Q;
#
# V[n](R, Q) := (R - 2 * Q) * V[n-2](R, Q) - Q^2 * V[n-4](R, Q);
# V[0](R, Q) := 2;
# V[1](R, Q) := 1;
# V[2](R, Q) := R - 2 * Q;
# V[3](R, Q) := R - 3 * Q;
#
# for all n:  U[2*n] = U[n](R, Q) * V[n](R, Q)
#
# for even n: V[2*n](R, Q) * 2 = V[n](R, Q)^2 + R * (R - 4*Q) * U[n](R,Q)^2
# for odd n:  V[2*n](R, Q) * 2 = R * V[n](R, Q)^2 + (R - 4*Q) * U[n](R,Q)^2
#
# for all n:  U[2*n+1](R, Q) * 2 = R * U[2*n](R, Q) + V[2*n](R, Q)
# for all n:  V[2*n+1](R, Q) * 2 = ((R - 4*Q) * U[2*n](R, Q) + V[2*n](R, Q))

class LehmerSequenceComputer(object):
    #Lehmer sequence = Lucas sequence with P = sqrt(R)
    #Recurrences modified to remove a multiple of sqrt(R)
    __slots__ = ("_uMemo", "_vMemo", "_r", "_q", "_mod")
    def __init__(self, r, q, mod):
        r = r % mod
        q = q % mod
        self._r = r
        self._q = q
        self._mod = mod
        self._uMemo = {0: 0, 1: 1, 2: 1, 3: (r - q) % mod}
        self._vMemo = {0: 2, 1: 1, 2: (r - 2 * q) % mod, 3: (r - 3 * q) % mod}

        div2 = (mod + 1) // 2
        if (div2 * 2) % mod != 1:
            raise ValueError("no inverse to 2 with modulus %r" % (mod,))

    def _calc(self, k):
        R = self._r
        Q = self._q
        mod = self._mod
        uMemo = self._uMemo
        vMemo = self._vMemo

        bits = k.bit_length() - 1
        div2 = (mod + 1) // 2

        for ii in range(1, bits+1):
            key = (k >> ii)
            if key in uMemo:
                U_i = uMemo[key]
                V_i = vMemo[key]
                bits = ii - 1 #only need to process the bits that were shifted off
                break
        else:
            U_i = 0
            V_i = 2

        for ii in range(bits, 0-1, -1):
            U_2i = (U_i * V_i) % mod
            if (k >> (ii + 1)) & 1: #was prev index odd?
                V_2i = ((R * V_i * V_i + (R - 4*Q) * U_i * U_i) * div2)  % mod
            else:
                V_2i = ((V_i * V_i + R * (R - 4*Q) * U_i * U_i) * div2) % mod

            uMemo[(k >> ii) & ~1] = U_2i
            vMemo[(k >> ii) & ~1] = V_2i
            if (k >> ii) & 1: #is current index odd?
                U_2ip1 = ((R * U_2i + V_2i) * div2) % mod
                V_2ip1 = (((R - 4*Q) * U_2i + V_2i) * div2) % mod
                uMemo[k >> ii] = U_2ip1
                vMemo[k >> ii] = V_2ip1
                U_i = U_2ip1
                V_i = V_2ip1
            else:
                U_i = U_2i
                V_i = V_2i

        return (U_i, V_i)

    def u(self, k):
        if k not in self._uMemo:
            self._calc(k)
        return self._uMemo[k]

    def v(self, k):
        if k not in self._vMemo:
            self._calc(k)
        return self._vMemo[k]

    def v_sqr(self, k):
        n = self._mod
        if (k & 1):
            return (pow(self.v(k), 2, n) * self._r) % n
        else:
            return pow(self.v(k), 2, n)

    def uv(self, k):
        if k not in self._uMemo:
            self._calc(k)
        return (self._uMemo[k], self._vMemo[k])

_tinyPrimes = frozenset([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191])
_tinyPrimeProduct = 0x24776ffd3cbd21c872eccd26ad078c5ba0586e2e57cf68515e3c4828a673a6e #Primes 2 to 191
_smallPrimeProducts = ( #Products containing all primes from 193 to 23029
    #Note: No product below contains two primes whose product is <= 23029, so if gcd(n, prod) != 1, the gcd is either n or a factor of n
    0xf0b12992ef8b81c547634eea1fd5c9fc538d370587f39659fb398972cffbf783, 0xf0b3b7671ec5b6e5e25d0675e9c16fd7a30417c2f5e25ba7a281314c9be0bead,
    0xf0b3d8c409c87fe8c6c762a1203f49cf5371e52a6b5fa52dcd9fc0ad5c6a9ab5, 0xf0b41dbd5e708420183e03ee153be61e4170c1576436076dc4969d57aabcd7d5,
    0xf0b508af3b8c4678520337591a3fcd41f2640c6b4cf5ed93e7ad037f7a5aaea9, 0xf0b53ed041fd15c397d88dae674b9f265c429aac1d7e93abad52f25361613c59,
    0xf0b58d076f49988dd7ece3ec92116c682ba1b0123e07de91a6ad2ea3647a8add, 0xf0b5c651c40ebf34749f905b17547c4f76769a8622468ee9ef10c5a374790d4b,
    0xf0b5f669ea7ca5033b5ce8ed2199eb0776a5dffde67c4ec38713c7f04877ffc9, 0xf0b619115a99ffb6a3f1fb7a06846d5d27655841b2f528c3648bd8f76da98935,
    0xf0b61ee681feb5d7abd940c4b257f2b741015b3e37504f2f63852950ec04efbb, 0xf0b6293a7e253db3fb6ffff806745da4f44786cd4f1d5dc864e25f3b86ada53f,
    0xf0b66a8c330f6ac0d48c7b876f73c3d5824fcfce3323b219e21d6109c5262243, 0xf0b67415f3041494074193480f4c9cb8c1c2925daa6d8d8b51c7590ec3961e1d,
    0xf0b67c1a8bd13a255742c0e6402ca0af76ebb24b6da4e8784e2b41a72d0973f7, 0xf0b691d4b889b9213a42c7f4cb9d30f95a4b7b3cd232058ce4cd86ef81047d89,
    0xf0b6aa21c614ff60d140f8aa318ee9ea3579a7ef5e71b22b72328bcd1b688799, 0xf0b6bc3384ce25a149cd648de4883bb48fab0f36303a83c155c216536effcf53,
    0xf0b6e31bf3736d1d077b47e957002a1cef3ef9f7f74d2d74a5f189c1212f66a3, 0xf0b73742581dff819b94af1ae47990bc381a0e7f274add69096734fc5b54b417,
    0xf0b76a3cc0b105e5935147f2c71d076481422d8756f852fda25d7efaa167e309, 0xf0b76ede0a6ad031740ff096a439c9ec8347955fb092abc26d6aa46d6cb1b661,
    0xf0b784a8672c5fe26bc3898788455abb3556749391df80928495a3a5427e6053, 0xf0b789679b8cb36c1a70e7e1e20dbf2fc3cf985c2239cc1744b238f11bdb72ab,
    0xf0b7e84f64019a8e247fa3dffb5c2c0093e76a16513ac80c033d6475694a8a3b, 0xf0b8234e3cae929038f931d1740f2fa8834dd99bfc658a4b59eb845d3ffad3bb,
    0xf0b824aae76ce20951746cd5c4b03fc8e1475d5cabeb2562b811a69098fad943, 0xf0b83093e3a104f4c0e030b35d787a239f80dcace0960da887a7181996101c83,
    0xf0b84087a080831948146ae6dcc7ae2b8f03e9dfeea1c9263442739b3517443b, 0xf0b87379ffc50fbc9f24f93948971c3003d0d8d58e72610cf6ea2bc805ab4fb5,
    0xf0b874e6227c478fc44725a08bbe76cd780845ff08b1ba7fcded243093980b25, 0xf0b87fc8fa082d8d5825477314c8373d013601db76451a441510e701d1c05b2b,
    0xf0b87fd347629ef63db3b16db23ea27a6d13e0d45e097efd651ab5dea38f63af, 0xf0b89659246415c26ef7f4e097a0b70d7103b307f3f50107d7ca1bdd2563b7eb,
    0xf0b8a7ccb93cf01bb7437692f26d6ebc681157c7391c4e600b6d9cbcb82146db, 0xf0b8d3a2d2800c049c1c3df8d2e4d5d0079f0ae05acccfb335bb5749963eece9,
    0xf0b8d6c39ce0c5c73c2802cafe4bb28f95356fe978eb5c7876d2ca5fe42e9bad, 0xf0b8de933fc4198b62ebd1ca7bbbc0f36b8a2f0af316673aa2a0b58a0234fcdd,
    0xf0b8e4d833001fea1a96b852737576cd075c5d86ef68ab930ce3a7acc3c87fef, 0xf0b8eb08a958d9f6bbf77f16dbce1b024fa3e95f0acc1ab4291f02b267596061,
    0xf0b90b332dc0836df05554f6eddf655887ec27a47c9e69496f328d54a59758d3, 0xf0b9195a7fc04b74be7df65c6e766ab513574e311dea381232c5e88f8bc881bf,
    0xf0b93bec17cc2afdc15f953729ae7866c2b7c35c4fec5fba48fff38c57f51cb7, 0xf0b94d816f0c16d066dc68e045acf249c7e75f57bf6c1a38222d262c26e08d13,
    0xf0b96b4fc2871dd09d5f29b6ba9937857536edd4481427d7461a5b327cf66233, 0xf0b96ca06c3687719edbb39a982869397e51b0100ee7c4ab2f1434f262766ec1,
    0xf0b97e689439ad7bd936364e4861210bbbe8d618ce62acd716b189c7ddc0d369, 0xf0b988d3fb06c2eb0629b5ec3dd2e47e71d48b21cd4bea542beaf2cdd388c9b3,
    0xf0b9b6ae75684090897f6ed767513cd4cb04268ce130b5d77916fd19bcad8895, 0xf0b9da1379cd2b2d4eaa326a0387436c38515d01456344bb34cce8e4c1558135,
    0xf0b9ebc4863627bdf412776635d37fa084dfcf3a80f0f41ec935eb13ff023e35, 0xf0b9fc05fd0225dd82454d22cff02956d8ba95747b92e844136ef7cc41e92397,
    0xf0ba277991f9a5ef68f904b61514aa3efa0fe9ce0ca9d3b87ae669a2d0bd26df, 0xf0ba5caad14f29c7953c797c841c5706b89948e1792e6e1695b85dde055047bf,
    0xf0ba6be2c0f41604d4a8caacbad2003263aa129fc8c800413fa583e0d05bccdd, 0xf0ba789802fcac23bad92f2f86babd33e5c6ee4101852342329398a525454513,
    0xf0ba86a3b6f08de12a1784dec44de26d7cea8268a7bc9b58cfd93fdeb3edfff9, 0xf0bab92173050400024e9e410b118ba92a140c0406e9143fc9796f516a89ad37,
    0xf0baba49f3e40fc02404c45ef0b352e6914d781dc449f97cadbede1601968461, 0xf0babe10edd7c6a51a03c13c0cb28638e4f48130f7de8d7cfb7155cc74d9fb5d,
    0xf0babee633821fba9353b11811650df4f07e57452ec0bbda3b6adee891c38091, 0xf0bb07809cf3cfdc7d8649b2bb53a171c06bbc755837c34b744f0a5caf4f9261,
    0xf0bb08317da71ec02da76a0da7886c4b31d125ff9f63b85736ec130656012ed9, 0xf0bb0dd0b8dd5f2639a3c0da5ec3ab8db28194253ded386721c6535d8a75bddd,
    0xf0bb2af1f49306a40d7faeaa5c21d96d905be0e1718b32020d6181ea4c5ebd73, 0xf0bb40959e34edc95424514262c60be6aea1753db958ab29f037fb5be9fadf99,
    0xf0bb47688b5ad1596c6950a83521fbb37e4da5931d7e20f154d8ed10328563c5, 0xf0bb4edab1d7532ee55aa17dd961ce75c66d1f36bcb5ff09dde3e7ee7aebc59f,
    0xf0bb59322274066cc65f215afcc6253e7e83b3f1d3c7ad9857902c0e01a531d9, 0xf0bb6229b56cdef76adc1f875f0f956a86a49cedd148690eea606510f6f75b99,
    0xf0bb72d5b03a5bc86e2f925edb70b3a70a83a8565304e8d7527c2445ef72fff3, 0xf0bb86e1e3e049097678086b5a2d1776241135c3987aab67031e2771455e8655,
    0xf0bba45ddcf417cfc1ae6730e605a31e1382e48351c7e058400c08828c282a89, 0xf0bbc443249e73da9c2a85e3752cf55d3744c83ce630feef068ef4d64151b8ef,
    0xf0bbe758b62c80118696ef3cd05a41f89bc6532f40fa7fa3dd39e45568d43d0d, 0xf0bbebda722555437dfc1f014cf7b2375353ee7c8e2568a71613b639ca05438d,
    0xf0bbf1f53793d05ce59971b8c9a77491ff7db929bd16c1949b18f30f58590fb1, 0xf0bc09e0fc545b48d58cf44f3e61c7c6e21dd75ae854f04f3e3f14fc93c41c59,
    0xf0bc18e3d6800bb5329aefb457035e1fac5a53ec59e52f6128c739871d4c211d, 0xf0bc1f092d7aa9df1d0d53c2fcaeb0047a2084c7da46a4380937ffab263bea69,
    0xf0bc443a0968a09c6ab5bf7ca7df7a7583c0775b1f2a6288a1ae8f02683b493b, 0xf0bc53ac970770d62a4955c0dc6cdb80c1e94044b8a6ba50dcda7055bc857c65,
    0xf0bc7bd93df5bbaf7944ef6ed9424252cdf6fa1cd844f591145189cab61b222f, 0xf0bc83db4ef74329a469644e26033a00c0d79b63d6c17c72e224f14ac835d3df,
    0xf0bca134473317cc4928c1a15450b449f57e4b1e5038bc440958c5b411de3d3d, 0xf0bcca66bf88e9829a345d567fa9997a6822db200d3aad1a03e1090d90059f5d,
    0xf0bcdc1f4979f2c26beac4c74292cb5c58c2697e17d15dc26b25a1276c1d4c69, 0xf0bcf30342ba3bae35884a2aadf45741694b4c725b6455ceb2cb219fbbed95b1,
    0xf0bd17ec50b93b71c5c6fd2c3e5976fe090d630e998e92fd9a6122599779b327, 0xf0bd68b767c3e3f829564bfb4e4cd3114ae844bc9f05d08f508d1e6ec2cdb65f,
    0xf0bd73f1ef4c82fb0c069337fdd30706a14cee221ee4b537a48c0de6fa7d184b, 0xf0bd86701e1725e1d21b4c7ce7deb360f37c15b74690b0063689671e4328a053,
    0xf0bdc43246df15624b067b919b5ae4746e7afe7199e21cf291bbbff3fe85bd6d, 0xf0bdc955b45efaef6e8bb19f31eade71d331692e3d94e9cecba5aa1642b1f315,
    0xf0be11675f15a69b00f5397501ba9fed8d5eaaceb8de3c661c2bfd6001526b5b, 0xf0be26469b2ef62860375e02b8fcdbd15ef5359785743d1c28f21550838e7543,
    0xf0be5b6c3081fbd75b0a70f2d7980b16d8c8a6172cf435167cfd0e0624bba231, 0xf0be9f3ef56ab22d34157477d117d82ba7da29268ac231a42ed26b419ea1fbc5,
    0xf0becf03d0d0786643956a5775be2eb5d140bd7252e909d9ef5ee6d82149ebcb, 0xf0bedb41904507efcc8b1a4f5312b1a2d908cccb4e697fb42b5578cdf92f2bd1,
    0xf0befa63c540f9a9e10db2e0d4ad9387b9972c58438a17fcc17c157ca2470fdf, 0xf0bf11e611e1c64874403988cbb5ebf74831fcbfa644eabd2974cb4eba867a13,
    0xf0bf1539d32ac8b2cbc4d7e8af6dd38bef0499ea367bff151cc71f4f8fad4bdf, 0xf0bf26fa50161661d611f4e686678cff9af17e62192224804f78c0c4b9209345,
    0xf0bf3210f76d1173cc16302bd71dc94a680ea53115244e1e216ad2e6bb3ecb91, 0xf0bf3fb4f937d2a8c8c8d06a12127f478a5b00feef73522c48173aa935a37753,
    0xf0bf41b6aac58218bf412eac7b3add3179d244517d9ba1e334a725edc64f1f65, 0xf0bf5b25e182bf46c592a00b500ea3768b018c85fd6729cafc7f5022be958fc9,
    0xf0bf6b4a808581a9f3ba9683d4146459bd6a694fd4eeceb4d7bb5177413e3017, 0xf0bfeae26302ddbd253a42142e6e5fedcb286a9fb83c77ee814159eba4aecc33,
    0xf0c015ab5ccd2646e8b6c2bebdd7de8d830031ecab84105a0f9a28f7da7005e5, 0xf0c016f081cca6bf621844519a3f14750c158654feb8af24fa58e14e23e53d8f,
    0xf0c07c159e43b2379fbd9d94ba3b1d06ff840bf265aeeb9d9a37342b5e55810f, 0xf0c0f70cd48c5da950577924cf3371404fbe20fc8404679d8fb0b8baa459f729,
    0xf0c13fba0f8c6592dd8f6e4e70c49163eca68352ec2024b7eecb7ccf6becef1d, 0xf0c1602de4169c419b997ad90fe646b525b92f4d8f896351130d8a598bb619d7,
    0xf0c17d90c4b3baedc6fc527312cbadfd804d968134f613c0b772c6422fab1027, 0xf0c17e27997ae15e319e78aaa50310b9df39ab896b63f5713cc3ead992764837,
    0xf0c1935246756e54db1b2a5a206dda4ad70ae7091fbf9cd7d1d0880282cce7d9, 0xf0c1b12eac191636b58fba296ad72aea52dc4dec9de98aad80e6eb9fb83fc46d,
    0xf0c1c914774dbcc98871fd25104dbf73e9e02c388ca4109c991f7880203f7145, 0xf0c261064514ba9db2970b7b3adc4f0b394d93a62721575c83fc7579795c1143,
    0xf0c28a1aee625c840d024f0129a3eeb01409f9f166554d1b7615b3bb9978db5f, 0xf0c292cc74d2ce7ade802a5160b52fb4e6ffd8025e5e4b473ea2affb8ed4079b,
    0xf0c2ba5783a5f49602cc83aa59fe4eaf30c6e88fa6835fd977271f01fb354843, 0xf0c34aa1137f3d63ddf79259f3c966b0f7c212fced0397c2005074f1c6e80ecd,
    0xf0c43bbb54cf79f58653e097cb84a1855b4da4890b068d93eb86cbd8fefbad47, 0xf0c76315da810f414c45ac59918c5a33c9f28085eb3dd5aa01eee87d5f69e4f3,
)

def TestSmallDivisors(n):
    global _tinyPrimeProduct, _tinyPrimes, _smallPrimeProducts
    if n < 2:
        return False
    gg = gcd(n, _tinyPrimeProduct)
    if gg != 1:
        return (n in _tinyPrimes)
    #Tiny primes has factors for all numbers < 37249 (193^2)
    if n < 37249:
        return True
    for pp in _smallPrimeProducts:
        gg = gcd(n, pp)
        if (gg != 1):
            return False #(gg == n) and (gg <= 23029)
    return True

def MillerRabinMultiWitnessPrimalityTest(n):
    global _tinyPrimes
    alist = [a % n for a in _tinyPrimes]
    if 0 in alist:
        return True
    n_1 = n - 1
    r, d = SplitInt(n_1)
    roots = set()
    for a in alist:
        x = pow(a, d, n)
        if (x == 1) or (x == n_1):
            continue
        for uu in range(r - 1):
            prevx = x
            x = (x * x) % n
            if x == 1:
                return False
            elif x == n_1:
                roots.add(prevx)
                roots.add(n - prevx)
                if len(roots) > 2:
                    return False
                break
        else:
            return False
    return True

def ExtendedLehmerPrimalityTest(n):
    #"Extensions in the Theory of Lucas and Lehmer Pseudoprimes"
    modroot = None
    for seqStart in (2, 3, 4, 5):
        for desiredDSign in (+1, -1):
            for D in range(seqStart, n, 4):
                dSign = Jacobi(D, n)
                if dSign == 0:
                    return False
                elif dSign == desiredDSign:
                    break
            else:
                raise ValueError("D has wrong sign!")

            for R in range(D + 8, n, 4):
                rSign = Jacobi(R, n)
                if rSign == 0:
                    return False
                elif rSign != dSign:
                    break
            else:
                raise ValueError("R has wrong sign!")

            Q = (R - D) // 4
            qSign = Jacobi(Q, n)
            if qSign == 0:
                return False

            if gcd(2 * R * Q * D, n) != 1:
                return False

            Q %= n
            R %= n
            D %= n

            l = LehmerSequenceComputer(R, Q, n)
            J = dSign * rSign

            s, d = SplitInt(n - J)
            #"Lehmer Test"
            if l.u(n - J) != 0:
                return False

            #"Euler Lehmer Test"
            if Jacobi(R * Q, n) == +1:
                if l.u((n - J) // 2) != 0:
                    return False
            else:
                if l.v((n - J) // 2) != 0:
                    return False

            #"Strong Lehmer Test"
            if (l.u(d) != 0) and all(l.v(d << r) != 0 for r in range(0, s)):
                return False

            #"Strong Lehmer 2 Test"
            if l.v(d << s) != (2 * rSign * pow(Q, (1 - J) // 2, n)) % n:
                return False

            A = lambda i: (l.v(d<<(s-i)) + 2 * pow(Q, d << (s - i - 1), n)) % n

            if modroot is None:
                modroot = PrimeModRootFinder(n)

            for ii in range(0, s - 1):
                plus, minus = modroot.root(A(ii))
                if plus is None:
                    return False
                if l.v(d << (s - ii - 1)) not in (plus, minus):
                    return False

            if (d & 1):
                plus, minus = modroot.root(A(s - 1) * ModInverse(R, n))
            else:
                plus, minus = modroot.root(A(s - 1))
            if plus is None:
                return False
            if l.v(d) not in (plus, minus):
                return False

    return True

def IsPrime(n):
    if n < 2:
        return False
    if not TestSmallDivisors(n):
        return False
    if not MillerRabinMultiWitnessPrimalityTest(n):
        return False
    if not ExtendedLehmerPrimalityTest(n):
        return False
    return True

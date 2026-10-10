import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures1822To2041

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e2042 : ℝ := e2022 - e2040
lemma b2042 : Encl e2042 (18966691087 / 200000000000 : ℝ) (94833455441 / 1000000000000 : ℝ) := by
  exact Encl.sub b2022 b2040 (by norm_num) (by norm_num)

def e2043 : ℝ := e2042 / e2027
lemma b2043 : Encl e2043 (7968281141 / 125000000000 : ℝ) (63746249133 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2042 b2027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2044 : ℝ := e2043 ^ 2
lemma b2044 : Encl e2044 (4063584277 / 1000000000000 : ℝ) (4063584279 / 1000000000000 : ℝ) := by
  exact Encl.pow b2043 (by norm_num) 2 (by norm_num) (by norm_num)

def e2045 : ℝ := e9 * e2044
lemma b2045 : Encl e2045 (1137803597 / 1000000000000 : ℝ) (1137803599 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2046 : ℝ := e2040 ^ 3
lemma b2046 : Encl e2046 (5154624719 / 1000000000000 : ℝ) (64432809 / 12500000000 : ℝ) := by
  exact Encl.pow b2040 (by norm_num) 3 (by norm_num) (by norm_num)

def e2047 : ℝ := e2030 * e2046
lemma b2047 : Encl e2047 (276339827 / 200000000000 : ℝ) (21589049 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b2030 b2046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2048 : ℝ := e2045 + e2047
lemma b2048 : Encl e2048 (629875683 / 250000000000 : ℝ) (503900547 / 200000000000 : ℝ) := by
  exact Encl.add b2045 b2047 (by norm_num) (by norm_num)

def e2049 : ℝ := min e2041 e2048
lemma b2049 : Encl e2049 (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  exact Encl.min b2041 b2048 (by norm_num) (by norm_num)

def e2050 : ℝ := (13 / 10 : ℝ)
lemma b2050 : Encl e2050 (13 / 10 : ℝ) (13 / 10 : ℝ) := by
  exact Encl.exact (13 / 10 : ℝ)

def e2051 : ℝ := e2050 / e0
lemma b2051 : Encl e2051 (206901426019 / 500000000000 : ℝ) (413802852039 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2050 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2052 : ℝ := e2050 * e7
lemma b2052 : Encl e2052 (22154928699 / 25000000000 : ℝ) (886197147963 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2050 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2053 : ℝ := e8 * e2050
lemma b2053 : Encl e2053 (637 / 500 : ℝ) (637 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2054 : ℝ := e2053 / e0
lemma b2054 : Encl e2054 (202763397499 / 500000000000 : ℝ) (405526794999 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2053 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2055 : ℝ := e2050 ^ 2
lemma b2055 : Encl e2055 (169 / 100 : ℝ) (169 / 100 : ℝ) := by
  exact Encl.pow b2050 (by norm_num) 2 (by norm_num) (by norm_num)

def e2056 : ℝ := e17 * e2055
lemma b2056 : Encl e2056 (169 / 25 : ℝ) (169 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2057 : ℝ := e2056 / e0
lemma b2057 : Encl e2057 (1075887415301 / 500000000000 : ℝ) (2151774830603 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2056 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2058 : ℝ := e5 + e2057
lemma b2058 : Encl e2058 (1575887415301 / 500000000000 : ℝ) (3151774830603 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2057 (by norm_num) (by norm_num)

def e2059 : ℝ := Real.sqrt e2058
lemma b2059 : Encl e2059 (1775323866397 / 1000000000000 : ℝ) (1775323866399 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2058 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2060 : ℝ := e5 + e2059
lemma b2060 : Encl e2060 (2775323866397 / 1000000000000 : ℝ) (2775323866399 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2059 (by norm_num) (by norm_num)

def e2061 : ℝ := e23 / e2060
lemma b2061 : Encl e2061 (720636616221 / 1000000000000 : ℝ) (360318308111 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2062 : ℝ := e9 * e2061
lemma b2062 : Encl e2062 (201778252541 / 1000000000000 : ℝ) (201778252543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2063 : ℝ := e2054 + e2062
lemma b2063 : Encl e2063 (607305047539 / 1000000000000 : ℝ) (303652523771 / 500000000000 : ℝ) := by
  exact Encl.add b2054 b2062 (by norm_num) (by norm_num)

def e2064 : ℝ := e2063 - e5
lemma b2064 : Encl e2064 (-392694952461 / 1000000000000 : ℝ) (-196347476229 / 500000000000 : ℝ) := by
  exact Encl.sub b2063 b5 (by norm_num) (by norm_num)

def e2065 : ℝ := e0 / e2055
lemma b2065 : Encl e2065 (929465282127 / 500000000000 : ℝ) (371786112851 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2066 : ℝ := e2051 ^ 2
lemma b2066 : Encl e2066 (85616400177 / 500000000000 : ℝ) (42808200089 / 250000000000 : ℝ) := by
  exact Encl.pow b2051 (by norm_num) 2 (by norm_num) (by norm_num)

def e2067 : ℝ := e5 - e2066
lemma b2067 : Encl e2067 (207191799911 / 250000000000 : ℝ) (414383599823 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2066 (by norm_num) (by norm_num)

def e2068 : ℝ := Real.sqrt e2067
lemma b2068 : Encl e2068 (910366519399 / 1000000000000 : ℝ) (910366519401 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2067 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2069 : ℝ := e29 - e2068
lemma b2069 : Encl e2069 (-48739970547 / 200000000000 : ℝ) (-60924963183 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2068 (by norm_num) (by norm_num)

def e2070 : ℝ := e2068 ^ 3
lemma b2070 : Encl e2070 (75448191093 / 100000000000 : ℝ) (94310238867 / 125000000000 : ℝ) := by
  exact Encl.pow b2068 (by norm_num) 3 (by norm_num) (by norm_num)

def e2071 : ℝ := e2070 / e35
lemma b2071 : Encl e2071 (25149397031 / 100000000000 : ℝ) (31436746289 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b2070 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2072 : ℝ := e2069 + e2071
lemma b2072 : Encl e2072 (311764703 / 40000000000 : ℝ) (389705879 / 50000000000 : ℝ) := by
  exact Encl.add b2069 b2071 (by norm_num) (by norm_num)

def e2073 : ℝ := e8 * e2072
lemma b2073 : Encl e2073 (7638235223 / 1000000000000 : ℝ) (7638235229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2072 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2074 : ℝ := e2066 / e2068
lemma b2074 : Encl e2074 (47023038717 / 250000000000 : ℝ) (188092154871 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2066 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2075 : ℝ := e2074 - e23
lemma b2075 : Encl e2075 (-452976961283 / 250000000000 : ℝ) (-1811907845129 / 1000000000000 : ℝ) := by
  exact Encl.sub b2074 b23 (by norm_num) (by norm_num)

def e2076 : ℝ := e23 * e2068
lemma b2076 : Encl e2076 (910366519399 / 500000000000 : ℝ) (910366519401 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2077 : ℝ := e2075 + e2076
lemma b2077 : Encl e2077 (4412596833 / 500000000000 : ℝ) (8825193673 / 1000000000000 : ℝ) := by
  exact Encl.add b2075 b2076 (by norm_num) (by norm_num)

def e2078 : ℝ := e2077 / e43
lemma b2078 : Encl e2078 (176503873 / 1000000000000 : ℝ) (88251937 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2077 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2079 : ℝ := e2073 - e2078
lemma b2079 : Encl e2079 (7461731349 / 1000000000000 : ℝ) (1865432839 / 250000000000 : ℝ) := by
  exact Encl.sub b2073 b2078 (by norm_num) (by norm_num)

def e2080 : ℝ := e2065 * e2079
lemma b2080 : Encl e2080 (6935420233 / 500000000000 : ℝ) (86692753 / 6250000000 : ℝ) := by
  exact Encl.mul_nonneg b2065 b2079 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2081 : ℝ := e2064 + e2080
lemma b2081 : Encl e2081 (-75764822399 / 200000000000 : ℝ) (-189412055989 / 500000000000 : ℝ) := by
  exact Encl.add b2064 b2080 (by norm_num) (by norm_num)

def e2082 : ℝ := e2052 ^ 2
lemma b2082 : Encl e2082 (196336346263 / 250000000000 : ℝ) (392672692529 / 500000000000 : ℝ) := by
  exact Encl.pow b2052 (by norm_num) 2 (by norm_num) (by norm_num)

def e2083 : ℝ := e5 - e2082
lemma b2083 : Encl e2083 (107327307471 / 500000000000 : ℝ) (53663653737 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2082 (by norm_num) (by norm_num)

def e2084 : ℝ := Real.sqrt e2083
lemma b2084 : Encl e2084 (463308336793 / 1000000000000 : ℝ) (579135421 / 1250000000 : ℝ) := by
  exact Encl.sqrt b2083 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2085 : ℝ := e5 + e2084
lemma b2085 : Encl e2085 (1463308336793 / 1000000000000 : ℝ) (1829135421 / 1250000000 : ℝ) := by
  exact Encl.add b5 b2084 (by norm_num) (by norm_num)

def e2086 : ℝ := e2052 / e2085
lemma b2086 : Encl e2086 (605612040657 / 1000000000000 : ℝ) (605612040663 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2085 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2087 : ℝ := e2086 ^ 2
lemma b2087 : Encl e2087 (91691485947 / 250000000000 : ℝ) (366765943797 / 1000000000000 : ℝ) := by
  exact Encl.pow b2086 (by norm_num) 2 (by norm_num) (by norm_num)

def e2088 : ℝ := e5 + e2087
lemma b2088 : Encl e2088 (341691485947 / 250000000000 : ℝ) (1366765943797 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2087 (by norm_num) (by norm_num)

def e2089 : ℝ := Real.sqrt e2088
lemma b2089 : Encl e2089 (23381753089 / 20000000000 : ℝ) (233817530891 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2088 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2090 : ℝ := e5 + e2089
lemma b2090 : Encl e2090 (43381753089 / 20000000000 : ℝ) (433817530891 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2089 (by norm_num) (by norm_num)

def e2091 : ℝ := e2086 / e2090
lemma b2091 : Encl e2091 (279201275897 / 1000000000000 : ℝ) (279201275901 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2086 b2090 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2092 : ℝ := Real.arcsin e2052
lemma b2092 : Encl e2092 (217814314373 / 200000000000 : ℝ) (1089071571881 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2052) (a := (279201275897 / 1000000000000 : ℝ)) (b := (279201275901 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (22154928699 / 25000000000 : ℝ) by norm_num).trans b2052.1
        exact b2052.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2052) (279201275897 / 1000000000000 : ℝ) (279201275901 / 1000000000000 : ℝ) from b2091) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2093 : ℝ := e59 * e2092
lemma b2093 : Encl e2093 (555426501651 / 1000000000000 : ℝ) (27771325083 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2092 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2094 : ℝ := e61 * e2052
lemma b2094 : Encl e2094 (173694641 / 400000000 : ℝ) (217118301251 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2095 : ℝ := e2094 * e2084
lemma b2095 : Encl e2095 (100592719039 / 500000000000 : ℝ) (201185438083 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2094 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2096 : ℝ := e2093 - e2095
lemma b2096 : Encl e2096 (22140066473 / 62500000000 : ℝ) (177120531791 / 500000000000 : ℝ) := by
  exact Encl.sub b2093 b2095 (by norm_num) (by norm_num)

def e2097 : ℝ := e43 * e2084
lemma b2097 : Encl e2097 (463308336793 / 20000000000 : ℝ) (579135421 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2098 : ℝ := e2052 / e2097
lemma b2098 : Encl e2098 (19127589071 / 500000000000 : ℝ) (1195474317 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2097 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2099 : ℝ := e2096 - e2098
lemma b2099 : Encl e2099 (19749117839 / 62500000000 : ℝ) (246863973 / 781250000 : ℝ) := by
  exact Encl.sub b2096 b2098 (by norm_num) (by norm_num)

def e2100 : ℝ := e5 + e2068
lemma b2100 : Encl e2100 (1910366519399 / 1000000000000 : ℝ) (1910366519401 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2068 (by norm_num) (by norm_num)

def e2101 : ℝ := e2051 / e2100
lemma b2101 : Encl e2101 (216609141667 / 1000000000000 : ℝ) (216609141669 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2051 b2100 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2102 : ℝ := e2101 ^ 2
lemma b2102 : Encl e2102 (46919520253 / 1000000000000 : ℝ) (9383904051 / 200000000000 : ℝ) := by
  exact Encl.pow b2101 (by norm_num) 2 (by norm_num) (by norm_num)

def e2103 : ℝ := e5 + e2102
lemma b2103 : Encl e2103 (1046919520253 / 1000000000000 : ℝ) (209383904051 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2102 (by norm_num) (by norm_num)

def e2104 : ℝ := Real.sqrt e2103
lemma b2104 : Encl e2104 (1023190852311 / 1000000000000 : ℝ) (1023190852313 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2105 : ℝ := e5 + e2104
lemma b2105 : Encl e2105 (2023190852311 / 1000000000000 : ℝ) (2023190852313 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2104 (by norm_num) (by norm_num)

def e2106 : ℝ := e2101 / e2105
lemma b2106 : Encl e2106 (21412625647 / 200000000000 : ℝ) (53531564119 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2101 b2105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2107 : ℝ := Real.arcsin e2051
lemma b2107 : Encl e2107 (213313695887 / 500000000000 : ℝ) (426627391787 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2051) (a := (21412625647 / 200000000000 : ℝ)) (b := (53531564119 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (206901426019 / 500000000000 : ℝ) by norm_num).trans b2051.1
        exact b2051.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2051) (21412625647 / 200000000000 : ℝ) (53531564119 / 500000000000 : ℝ) from b2106) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2108 : ℝ := e59 * e2107
lemma b2108 : Encl e2108 (54394992451 / 250000000000 : ℝ) (54394992453 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2109 : ℝ := e61 * e2051
lemma b2109 : Encl e2109 (101381698749 / 500000000000 : ℝ) (81105359 / 400000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2051 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2110 : ℝ := e2109 * e2068
lemma b2110 : Encl e2110 (184589008441 / 1000000000000 : ℝ) (46147252111 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2109 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2111 : ℝ := e2108 - e2110
lemma b2111 : Encl e2111 (412387017 / 12500000000 : ℝ) (32990961371 / 1000000000000 : ℝ) := by
  exact Encl.sub b2108 b2110 (by norm_num) (by norm_num)

def e2112 : ℝ := e43 * e2068
lemma b2112 : Encl e2112 (910366519399 / 20000000000 : ℝ) (910366519401 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2113 : ℝ := e2051 / e2112
lemma b2113 : Encl e2113 (1818181329 / 200000000000 : ℝ) (4545453323 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2051 b2112 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2114 : ℝ := e2111 - e2113
lemma b2114 : Encl e2114 (11950027357 / 500000000000 : ℝ) (11950027363 / 500000000000 : ℝ) := by
  exact Encl.sub b2111 b2113 (by norm_num) (by norm_num)

def e2115 : ℝ := e2099 - e2114
lemma b2115 : Encl e2115 (146042915349 / 500000000000 : ℝ) (146042915363 / 500000000000 : ℝ) := by
  exact Encl.sub b2099 b2114 (by norm_num) (by norm_num)

def e2116 : ℝ := e2115 / e2050
lemma b2116 : Encl e2116 (224681408229 / 1000000000000 : ℝ) (224681408251 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2115 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2117 : ℝ := e2081 + e2116
lemma b2117 : Encl e2117 (-77071351883 / 500000000000 : ℝ) (-154142703727 / 1000000000000 : ℝ) := by
  exact Encl.add b2081 b2116 (by norm_num) (by norm_num)

def e2118 : ℝ := e2052 + e4
lemma b2118 : Encl e2118 (187594046657 / 100000000000 : ℝ) (937970233287 / 500000000000 : ℝ) := by
  exact Encl.add b2052 b4 (by norm_num) (by norm_num)

def e2119 : ℝ := e2118 / e23
lemma b2119 : Encl e2119 (187594046657 / 200000000000 : ℝ) (937970233287 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2118 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2120 : ℝ := e2052 / e2050
lemma b2120 : Encl e2120 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2121 : ℝ := e89 * e2120
lemma b2121 : Encl e2121 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2122 : ℝ := e2120 ^ 2
lemma b2122 : Encl e2122 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2120 (by norm_num) 2 (by norm_num) (by norm_num)

def e2123 : ℝ := e91 * e2122
lemma b2123 : Encl e2123 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2124 : ℝ := e5 + e2123
lemma b2124 : Encl e2124 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2123 (by norm_num) (by norm_num)

def e2125 : ℝ := Real.sqrt e2124
lemma b2125 : Encl e2125 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2124 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2126 : ℝ := e2121 * e2125
lemma b2126 : Encl e2126 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2121 b2125 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2127 : ℝ := e97 * e2122
lemma b2127 : Encl e2127 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2128 : ℝ := e2126 - e2127
lemma b2128 : Encl e2128 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2126 b2127 (by norm_num) (by norm_num)

def e2129 : ℝ := e2119 * e2128
lemma b2129 : Encl e2129 (639405035073 / 1000000000000 : ℝ) (639405035097 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2119 b2128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2130 : ℝ := e2119 / e2050
lemma b2130 : Encl e2130 (144303112813 / 200000000000 : ℝ) (721515564067 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2131 : ℝ := e89 * e2130
lemma b2131 : Encl e2131 (639426520007 / 500000000000 : ℝ) (63942652001 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2130 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2132 : ℝ := e2130 ^ 2
lemma b2132 : Encl e2132 (130146177297 / 250000000000 : ℝ) (520584709191 / 1000000000000 : ℝ) := by
  exact Encl.pow b2130 (by norm_num) 2 (by norm_num) (by norm_num)

def e2133 : ℝ := e91 * e2132
lemma b2133 : Encl e2133 (51108284311 / 125000000000 : ℝ) (102216568623 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2134 : ℝ := e5 + e2133
lemma b2134 : Encl e2134 (176108284311 / 125000000000 : ℝ) (352216568623 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2133 (by norm_num) (by norm_num)

def e2135 : ℝ := Real.sqrt e2134
lemma b2135 : Encl e2135 (74184795509 / 62500000000 : ℝ) (1186956728147 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2136 : ℝ := e2131 * e2135
lemma b2136 : Encl e2136 (189742902519 / 125000000000 : ℝ) (1517943220163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2131 b2135 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2137 : ℝ := e97 * e2132
lemma b2137 : Encl e2137 (817732548977 / 1000000000000 : ℝ) (817732548983 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2138 : ℝ := e2136 - e2137
lemma b2138 : Encl e2138 (700210671169 / 1000000000000 : ℝ) (350105335593 / 500000000000 : ℝ) := by
  exact Encl.sub b2136 b2137 (by norm_num) (by norm_num)

def e2139 : ℝ := e2052 * e2138
lemma b2139 : Encl e2139 (620524699761 / 1000000000000 : ℝ) (620524699779 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2052 b2138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2140 : ℝ := e2129 - e2139
lemma b2140 : Encl e2140 (9440167647 / 500000000000 : ℝ) (2360041917 / 125000000000 : ℝ) := by
  exact Encl.sub b2129 b2139 (by norm_num) (by norm_num)

def e2141 : ℝ := e2119 ^ 2
lemma b2141 : Encl e2141 (13746689977 / 15625000000 : ℝ) (879788158533 / 1000000000000 : ℝ) := by
  exact Encl.pow b2119 (by norm_num) 2 (by norm_num) (by norm_num)

def e2142 : ℝ := e8 * e2141
lemma b2142 : Encl e2142 (862192395357 / 1000000000000 : ℝ) (862192395363 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2143 : ℝ := e5 - e2142
lemma b2143 : Encl e2143 (137807604637 / 1000000000000 : ℝ) (137807604643 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2142 (by norm_num) (by norm_num)

def e2144 : ℝ := e5 - e2141
lemma b2144 : Encl e2144 (120211841467 / 1000000000000 : ℝ) (1878310023 / 15625000000 : ℝ) := by
  exact Encl.sub b5 b2141 (by norm_num) (by norm_num)

def e2145 : ℝ := Real.sqrt e2144
lemma b2145 : Encl e2145 (173357896753 / 500000000000 : ℝ) (173357896757 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2146 : ℝ := e2143 / e2145
lemma b2146 : Encl e2146 (198732805391 / 500000000000 : ℝ) (39746561081 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2143 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2147 : ℝ := e5 - e2146
lemma b2147 : Encl e2147 (60253438919 / 100000000000 : ℝ) (301267194609 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2146 (by norm_num) (by norm_num)

def e2148 : ℝ := e8 * e2082
lemma b2148 : Encl e2148 (15392769547 / 20000000000 : ℝ) (769638477357 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2082 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2149 : ℝ := e5 - e2148
lemma b2149 : Encl e2149 (230361522643 / 1000000000000 : ℝ) (4607230453 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b2148 (by norm_num) (by norm_num)

def e2150 : ℝ := e2149 / e2084
lemma b2150 : Encl e2150 (9944199331 / 20000000000 : ℝ) (248604983287 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2149 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2151 : ℝ := e5 - e2150
lemma b2151 : Encl e2151 (251395016713 / 500000000000 : ℝ) (10055800669 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b2150 (by norm_num) (by norm_num)

def e2152 : ℝ := e2147 - e2151
lemma b2152 : Encl e2152 (4987217787 / 50000000000 : ℝ) (6234022237 / 62500000000 : ℝ) := by
  exact Encl.sub b2147 b2151 (by norm_num) (by norm_num)

def e2153 : ℝ := e2140 * e2152
lemma b2153 : Encl e2153 (11770043 / 6250000000 : ℝ) (941603443 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2140 b2152 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2154 : ℝ := e2138 - e2128
lemma b2154 : Encl e2154 (18520557341 / 1000000000000 : ℝ) (18520557381 / 1000000000000 : ℝ) := by
  exact Encl.sub b2138 b2128 (by norm_num) (by norm_num)

def e2155 : ℝ := e5 + e2145
lemma b2155 : Encl e2155 (673357896753 / 500000000000 : ℝ) (673357896757 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2145 (by norm_num) (by norm_num)

def e2156 : ℝ := e2119 / e2155
lemma b2156 : Encl e2156 (348243570693 / 500000000000 : ℝ) (696487141393 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2155 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2157 : ℝ := e2156 ^ 2
lemma b2157 : Encl e2157 (121273584529 / 250000000000 : ℝ) (242547169063 / 500000000000 : ℝ) := by
  exact Encl.pow b2156 (by norm_num) 2 (by norm_num) (by norm_num)

def e2158 : ℝ := e5 + e2157
lemma b2158 : Encl e2158 (371273584529 / 250000000000 : ℝ) (742547169063 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2157 (by norm_num) (by norm_num)

def e2159 : ℝ := Real.sqrt e2158
lemma b2159 : Encl e2159 (609322233739 / 500000000000 : ℝ) (1218644467483 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2158 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2160 : ℝ := e5 + e2159
lemma b2160 : Encl e2160 (1109322233739 / 500000000000 : ℝ) (2218644467483 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2159 (by norm_num) (by norm_num)

def e2161 : ℝ := e2156 / e2160
lemma b2161 : Encl e2161 (313924629021 / 1000000000000 : ℝ) (156962314513 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2156 b2160 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2162 : ℝ := Real.arcsin e2119
lemma b2162 : Encl e2162 (7604555603 / 6250000000 : ℝ) (152091112063 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e2119) (a := (313924629021 / 1000000000000 : ℝ)) (b := (156962314513 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (187594046657 / 200000000000 : ℝ) by norm_num).trans b2119.1
        exact b2119.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2119) (313924629021 / 1000000000000 : ℝ) (156962314513 / 500000000000 : ℝ) from b2161) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2163 : ℝ := e59 * e2162
lemma b2163 : Encl e2163 (155132934301 / 250000000000 : ℝ) (310265868609 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2164 : ℝ := e61 * e2119
lemma b2164 : Encl e2164 (459605414309 / 1000000000000 : ℝ) (459605414311 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2119 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2165 : ℝ := e2164 * e2145
lemma b2165 : Encl e2165 (159352455921 / 1000000000000 : ℝ) (159352455927 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2164 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2166 : ℝ := e2163 - e2165
lemma b2166 : Encl e2166 (461179281277 / 1000000000000 : ℝ) (461179281297 / 1000000000000 : ℝ) := by
  exact Encl.sub b2163 b2165 (by norm_num) (by norm_num)

def e2167 : ℝ := e43 * e2145
lemma b2167 : Encl e2167 (173357896753 / 10000000000 : ℝ) (173357896757 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2168 : ℝ := e2119 / e2167
lemma b2168 : Encl e2168 (6763249979 / 125000000000 : ℝ) (27052999917 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2169 : ℝ := e2166 - e2168
lemma b2169 : Encl e2169 (407073281443 / 1000000000000 : ℝ) (81414656293 / 200000000000 : ℝ) := by
  exact Encl.sub b2166 b2168 (by norm_num) (by norm_num)

def e2170 : ℝ := e2169 - e2099
lemma b2170 : Encl e2170 (91087396003 / 1000000000000 : ℝ) (91087396041 / 1000000000000 : ℝ) := by
  exact Encl.sub b2169 b2099 (by norm_num) (by norm_num)

def e2171 : ℝ := e2154 * e2170
lemma b2171 : Encl e2171 (84349467 / 50000000000 : ℝ) (843494673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2154 b2170 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2172 : ℝ := e2153 + e2171
lemma b2172 : Encl e2172 (178509811 / 50000000000 : ℝ) (446274529 / 125000000000 : ℝ) := by
  exact Encl.add b2153 b2171 (by norm_num) (by norm_num)

def e2173 : ℝ := e2119 - e2052
lemma b2173 : Encl e2173 (25886542661 / 500000000000 : ℝ) (51773085327 / 1000000000000 : ℝ) := by
  exact Encl.sub b2119 b2052 (by norm_num) (by norm_num)

def e2174 : ℝ := e2172 / e2173
lemma b2174 : Encl e2174 (68958536997 / 1000000000000 : ℝ) (68958537237 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2172 b2173 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2175 : ℝ := e2117 + e2174
lemma b2175 : Encl e2175 (-85184166769 / 1000000000000 : ℝ) (-8518416649 / 100000000000 : ℝ) := by
  exact Encl.add b2117 b2174 (by norm_num) (by norm_num)

def e2176 : ℝ := e4 * e2138
lemma b2176 : Encl e2176 (5414287761 / 7812500000 : ℝ) (693028833427 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2177 : ℝ := e4 / e2050
lemma b2177 : Encl e2177 (152268202863 / 200000000000 : ℝ) (761341014317 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2178 : ℝ := e89 * e2177
lemma b2178 : Encl e2178 (674720906337 / 500000000000 : ℝ) (1349441812679 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2177 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2179 : ℝ := e2177 ^ 2
lemma b2179 : Encl e2179 (289820070039 / 500000000000 : ℝ) (289820070041 / 500000000000 : ℝ) := by
  exact Encl.pow b2177 (by norm_num) 2 (by norm_num) (by norm_num)

def e2180 : ℝ := e91 * e2179
lemma b2180 : Encl e2180 (56906037681 / 125000000000 : ℝ) (455248301453 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2181 : ℝ := e5 + e2180
lemma b2181 : Encl e2181 (181906037681 / 125000000000 : ℝ) (1455248301453 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2180 (by norm_num) (by norm_num)

def e2182 : ℝ := Real.sqrt e2181
lemma b2182 : Encl e2182 (301584182013 / 250000000000 : ℝ) (241267345611 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2181 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2183 : ℝ := e2178 * e2182
lemma b2183 : Encl e2183 (1627881220997 / 1000000000000 : ℝ) (101742576313 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2178 b2182 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2184 : ℝ := e97 * e2179
lemma b2184 : Encl e2184 (56906037681 / 62500000000 : ℝ) (113812075363 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2185 : ℝ := e2183 - e2184
lemma b2185 : Encl e2185 (717384618093 / 1000000000000 : ℝ) (5604567329 / 7812500000 : ℝ) := by
  exact Encl.sub b2183 b2184 (by norm_num) (by norm_num)

def e2186 : ℝ := e2119 * e2185
lemma b2186 : Encl e2186 (672885417587 / 1000000000000 : ℝ) (84110677201 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b2119 b2185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2187 : ℝ := e2176 - e2186
lemma b2187 : Encl e2187 (100717079 / 5000000000 : ℝ) (125896349 / 6250000000 : ℝ) := by
  exact Encl.sub b2176 b2186 (by norm_num) (by norm_num)

def e2188 : ℝ := e165 - e2147
lemma b2188 : Encl e2188 (117465610757 / 1000000000000 : ℝ) (58732805419 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2147 (by norm_num) (by norm_num)

def e2189 : ℝ := e2187 * e2188
lemma b2189 : Encl e2189 (2366158639 / 1000000000000 : ℝ) (2366158647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2187 b2188 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2190 : ℝ := e2185 - e2138
lemma b2190 : Encl e2190 (17173946907 / 1000000000000 : ℝ) (17173946943 / 1000000000000 : ℝ) := by
  exact Encl.sub b2185 b2138 (by norm_num) (by norm_num)

def e2191 : ℝ := e183 - e2169
lemma b2191 : Encl e2191 (113079488047 / 1000000000000 : ℝ) (565397441 / 5000000000 : ℝ) := by
  exact Encl.sub b183 b2169 (by norm_num) (by norm_num)

def e2192 : ℝ := e2190 * e2191
lemma b2192 : Encl e2192 (1942021123 / 1000000000000 : ℝ) (1942021131 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2190 b2191 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2193 : ℝ := e2189 + e2192
lemma b2193 : Encl e2193 (2154089881 / 500000000000 : ℝ) (2154089889 / 500000000000 : ℝ) := by
  exact Encl.add b2189 b2192 (by norm_num) (by norm_num)

def e2194 : ℝ := e4 - e2119
lemma b2194 : Encl e2194 (51773085323 / 1000000000000 : ℝ) (25886542663 / 500000000000 : ℝ) := by
  exact Encl.sub b4 b2119 (by norm_num) (by norm_num)

def e2195 : ℝ := e2193 / e2194
lemma b2195 : Encl e2195 (16642545967 / 200000000000 : ℝ) (1664254603 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b2193 b2194 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2196 : ℝ := e2175 + e2195
lemma b2196 : Encl e2196 (-985718467 / 500000000000 : ℝ) (-98571817 / 50000000000 : ℝ) := by
  exact Encl.add b2175 b2195 (by norm_num) (by norm_num)

def e2197 : ℝ := e924 / e2050
lemma b2197 : Encl e2197 (738461538461 / 1000000000000 : ℝ) (369230769231 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2198 : ℝ := min e7 e2197
lemma b2198 : Encl e2198 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2197 (by norm_num) (by norm_num)

def e2199 : ℝ := e2198 - e5
lemma b2199 : Encl e2199 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2198 b5 (by norm_num) (by norm_num)

def e2200 : ℝ := e23 * e2050
lemma b2200 : Encl e2200 (13 / 5 : ℝ) (13 / 5 : ℝ) := by
  exact Encl.mul_nonneg b23 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2201 : ℝ := e2200 * e2061
lemma b2201 : Encl e2201 (936827601087 / 500000000000 : ℝ) (936827601089 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2200 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2202 : ℝ := e2201 / e0
lemma b2202 : Encl e2202 (596402974151 / 1000000000000 : ℝ) (596402974153 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2201 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2203 : ℝ := e2199 + e2202
lemma b2203 : Encl e2203 (278093087967 / 1000000000000 : ℝ) (27809308797 / 100000000000 : ℝ) := by
  exact Encl.add b2199 b2202 (by norm_num) (by norm_num)

def e2204 : ℝ := e23 * e2055
lemma b2204 : Encl e2204 (169 / 50 : ℝ) (169 / 50 : ℝ) := by
  exact Encl.mul_nonneg b23 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2205 : ℝ := e2204 * e2061
lemma b2205 : Encl e2205 (1217875881413 / 500000000000 : ℝ) (2435751762831 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2204 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2206 : ℝ := e0 + e2205
lemma b2206 : Encl e2206 (1115468883283 / 200000000000 : ℝ) (5577344416421 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2205 (by norm_num) (by norm_num)

def e2207 : ℝ := Real.sqrt e2206
lemma b2207 : Encl e2207 (1180820098111 / 500000000000 : ℝ) (94465607849 / 40000000000 : ℝ) := by
  exact Encl.sqrt b2206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2208 : ℝ := e932 * e2207
lemma b2208 : Encl e2208 (1503466844131 / 1000000000000 : ℝ) (187933355517 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2209 : ℝ := e2050 ^ 3
lemma b2209 : Encl e2209 (2197 / 1000 : ℝ) (2197 / 1000 : ℝ) := by
  exact Encl.pow b2050 (by norm_num) 3 (by norm_num) (by norm_num)

def e2210 : ℝ := e939 * e2209
lemma b2210 : Encl e2210 (147199 / 500000 : ℝ) (147199 / 500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2209 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2211 : ℝ := min e2210 e941
lemma b2211 : Encl e2211 (147199 / 500000 : ℝ) (147199 / 500000 : ℝ) := by
  exact Encl.min b2210 b941 (by norm_num) (by norm_num)

def e2212 : ℝ := e23 * e2203
lemma b2212 : Encl e2212 (278093087967 / 500000000000 : ℝ) (27809308797 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2203 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2213 : ℝ := e944 * e2211
lemma b2213 : Encl e2213 (441597 / 250000 : ℝ) (441597 / 250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2211 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2214 : ℝ := e2208 ^ 2
lemma b2214 : Encl e2214 (2260412551401 / 1000000000000 : ℝ) (2260412551417 / 1000000000000 : ℝ) := by
  exact Encl.pow b2208 (by norm_num) 2 (by norm_num) (by norm_num)

def e2215 : ℝ := e2213 * e2214
lemma b2215 : Encl e2215 (998191401461 / 250000000000 : ℝ) (3992765605873 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2213 b2214 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2216 : ℝ := e2215 * e2203
lemma b2216 : Encl e2216 (1110360516857 / 1000000000000 : ℝ) (555180258439 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2215 b2203 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2217 : ℝ := e2216 / e9
lemma b2217 : Encl e2217 (3965573274489 / 1000000000000 : ℝ) (793114654913 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2216 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2218 : ℝ := e5 + e2217
lemma b2218 : Encl e2218 (4965573274489 / 1000000000000 : ℝ) (993114654913 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2217 (by norm_num) (by norm_num)

def e2219 : ℝ := Real.sqrt e2218
lemma b2219 : Encl e2219 (1114178315451 / 500000000000 : ℝ) (55708915773 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2218 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2220 : ℝ := e5 + e2219
lemma b2220 : Encl e2220 (1614178315451 / 500000000000 : ℝ) (80708915773 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2219 (by norm_num) (by norm_num)

def e2221 : ℝ := e2212 / e2220
lemma b2221 : Encl e2221 (21535189553 / 125000000000 : ℝ) (43070379107 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2212 b2220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2222 : ℝ := e2211 * e954
lemma b2222 : Encl e2222 (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2211 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2223 : ℝ := e2203 - e2221
lemma b2223 : Encl e2223 (105811571539 / 1000000000000 : ℝ) (52905785773 / 500000000000 : ℝ) := by
  exact Encl.sub b2203 b2221 (by norm_num) (by norm_num)

def e2224 : ℝ := e2223 / e2208
lemma b2224 : Encl e2224 (70378387093 / 1000000000000 : ℝ) (70378387099 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2223 b2208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2225 : ℝ := e2224 ^ 2
lemma b2225 : Encl e2225 (4953117369 / 1000000000000 : ℝ) (4953117371 / 1000000000000 : ℝ) := by
  exact Encl.pow b2224 (by norm_num) 2 (by norm_num) (by norm_num)

def e2226 : ℝ := e9 * e2225
lemma b2226 : Encl e2226 (1386872863 / 1000000000000 : ℝ) (43339777 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2227 : ℝ := e2221 ^ 3
lemma b2227 : Encl e2227 (5113474061 / 1000000000000 : ℝ) (5113474063 / 1000000000000 : ℝ) := by
  exact Encl.pow b2221 (by norm_num) 3 (by norm_num) (by norm_num)

def e2228 : ℝ := e2211 * e2227
lemma b2228 : Encl e2228 (188174567 / 125000000000 : ℝ) (752698269 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2211 b2227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2229 : ℝ := e2226 + e2228
lemma b2229 : Encl e2229 (2892269399 / 1000000000000 : ℝ) (1446134701 / 500000000000 : ℝ) := by
  exact Encl.add b2226 b2228 (by norm_num) (by norm_num)

def e2230 : ℝ := min e2222 e2229
lemma b2230 : Encl e2230 (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  exact Encl.min b2222 b2229 (by norm_num) (by norm_num)

def e2231 : ℝ := (67 / 50 : ℝ)
lemma b2231 : Encl e2231 (67 / 50 : ℝ) (67 / 50 : ℝ) := by
  exact Encl.exact (67 / 50 : ℝ)

def e2232 : ℝ := e2231 / e0
lemma b2232 : Encl e2232 (213267623743 / 500000000000 : ℝ) (426535247487 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2231 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2233 : ℝ := e2231 * e7
lemma b2233 : Encl e2233 (913464752513 / 1000000000000 : ℝ) (182692950503 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2231 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2234 : ℝ := e8 * e2231
lemma b2234 : Encl e2234 (3283 / 2500 : ℝ) (3283 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2235 : ℝ := e2234 / e0
lemma b2235 : Encl e2235 (52250567817 / 125000000000 : ℝ) (418004542537 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2234 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2236 : ℝ := e2231 ^ 2
lemma b2236 : Encl e2236 (4489 / 2500 : ℝ) (4489 / 2500 : ℝ) := by
  exact Encl.pow b2231 (by norm_num) 2 (by norm_num) (by norm_num)

def e2237 : ℝ := e17 * e2236
lemma b2237 : Encl e2237 (4489 / 625 : ℝ) (4489 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2238 : ℝ := e2237 / e0
lemma b2238 : Encl e2238 (1143114463263 / 500000000000 : ℝ) (2286228926527 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2237 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2239 : ℝ := e5 + e2238
lemma b2239 : Encl e2239 (1643114463263 / 500000000000 : ℝ) (3286228926527 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2238 (by norm_num) (by norm_num)

def e2240 : ℝ := Real.sqrt e2239
lemma b2240 : Encl e2240 (906397943307 / 500000000000 : ℝ) (362559177323 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2241 : ℝ := e5 + e2240
lemma b2241 : Encl e2241 (1406397943307 / 500000000000 : ℝ) (562559177323 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2240 (by norm_num) (by norm_num)

def e2242 : ℝ := e23 / e2241
lemma b2242 : Encl e2242 (142207261431 / 200000000000 : ℝ) (177759076789 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2241 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2243 : ℝ := e9 * e2242
lemma b2243 : Encl e2243 (199090166003 / 1000000000000 : ℝ) (49772541501 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2244 : ℝ := e2235 + e2243
lemma b2244 : Encl e2244 (617094708539 / 1000000000000 : ℝ) (617094708541 / 1000000000000 : ℝ) := by
  exact Encl.add b2235 b2243 (by norm_num) (by norm_num)

def e2245 : ℝ := e2244 - e5
lemma b2245 : Encl e2245 (-382905291461 / 1000000000000 : ℝ) (-382905291459 / 1000000000000 : ℝ) := by
  exact Encl.sub b2244 b5 (by norm_num) (by norm_num)

def e2246 : ℝ := e0 / e2236
lemma b2246 : Encl e2246 (218700758353 / 125000000000 : ℝ) (69984242673 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2247 : ℝ := e2232 ^ 2
lemma b2247 : Encl e2247 (181932317347 / 1000000000000 : ℝ) (181932317349 / 1000000000000 : ℝ) := by
  exact Encl.pow b2232 (by norm_num) 2 (by norm_num) (by norm_num)

def e2248 : ℝ := e5 - e2247
lemma b2248 : Encl e2248 (818067682651 / 1000000000000 : ℝ) (818067682653 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2247 (by norm_num) (by norm_num)

def e2249 : ℝ := Real.sqrt e2248
lemma b2249 : Encl e2249 (113058867593 / 125000000000 : ℝ) (452235470373 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2248 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2250 : ℝ := e29 - e2249
lemma b2250 : Encl e2250 (-1486276713 / 6250000000 : ℝ) (-237804274077 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2249 (by norm_num) (by norm_num)

def e2251 : ℝ := e2249 ^ 3
lemma b2251 : Encl e2251 (739918446519 / 1000000000000 : ℝ) (184979611631 / 250000000000 : ℝ) := by
  exact Encl.pow b2249 (by norm_num) 3 (by norm_num) (by norm_num)

def e2252 : ℝ := e2251 / e35
lemma b2252 : Encl e2252 (246639482173 / 1000000000000 : ℝ) (9865579287 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2251 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2253 : ℝ := e2250 + e2252
lemma b2253 : Encl e2253 (8835208093 / 1000000000000 : ℝ) (4417604049 / 500000000000 : ℝ) := by
  exact Encl.add b2250 b2252 (by norm_num) (by norm_num)

def e2254 : ℝ := e8 * e2253
lemma b2254 : Encl e2254 (8658503931 / 1000000000000 : ℝ) (8658503937 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2253 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2255 : ℝ := e2247 / e2249
lemma b2255 : Encl e2255 (20114777507 / 100000000000 : ℝ) (100573887537 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2247 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2256 : ℝ := e2255 - e23
lemma b2256 : Encl e2256 (-179885222493 / 100000000000 : ℝ) (-899426112463 / 500000000000 : ℝ) := by
  exact Encl.sub b2255 b23 (by norm_num) (by norm_num)

def e2257 : ℝ := e23 * e2249
lemma b2257 : Encl e2257 (113058867593 / 62500000000 : ℝ) (452235470373 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2258 : ℝ := e2256 + e2257
lemma b2258 : Encl e2258 (5044828279 / 500000000000 : ℝ) (5044828283 / 500000000000 : ℝ) := by
  exact Encl.add b2256 b2257 (by norm_num) (by norm_num)

def e2259 : ℝ := e2258 / e43
lemma b2259 : Encl e2259 (201793131 / 1000000000000 : ℝ) (50448283 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2258 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2260 : ℝ := e2254 - e2259
lemma b2260 : Encl e2260 (8456710799 / 1000000000000 : ℝ) (4228355403 / 500000000000 : ℝ) := by
  exact Encl.sub b2254 b2259 (by norm_num) (by norm_num)

def e2261 : ℝ := e2246 * e2260
lemma b2261 : Encl e2261 (14795912519 / 1000000000000 : ℝ) (3698978133 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2246 b2260 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2262 : ℝ := e2245 + e2261

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI

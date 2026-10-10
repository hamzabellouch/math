import Mathlib
import OAI.Geometry.CubicTorus.Profiles.GainBounds

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
lemma b71 : Encl e71 (101059633423 / 100000000000 : ℝ) (1010596334231 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b70 (by norm_num) (by norm_num)

def e72 : ℝ := Real.sqrt e71
lemma b72 : Encl e72 (10052842057 / 10000000000 : ℝ) (1005284205701 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e73 : ℝ := e5 + e72
lemma b73 : Encl e73 (20052842057 / 10000000000 : ℝ) (2005284205701 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b72 (by norm_num) (by norm_num)

def e74 : ℝ := e69 / e73
lemma b74 : Encl e74 (12833404989 / 250000000000 : ℝ) (51333619957 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b69 b73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e75 : ℝ := Real.arcsin e12
lemma b75 : Encl e75 (102577201359 / 500000000000 : ℝ) (205154402723 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e12) (a := (12833404989 / 250000000000 : ℝ)) (b := (51333619957 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (203718327157 / 1000000000000 : ℝ) by norm_num).trans b12.1
        exact b12.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e12) (12833404989 / 250000000000 : ℝ) (51333619957 / 1000000000000 : ℝ) from b74) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e76 : ℝ := e59 * e75
lemma b76 : Encl e76 (52314372693 / 500000000000 : ℝ) (104628745389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e77 : ℝ := e61 * e12
lemma b77 : Encl e77 (49910990153 / 500000000000 : ℝ) (24955495077 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e78 : ℝ := e77 * e32
lemma b78 : Encl e78 (97728667613 / 1000000000000 : ℝ) (3054020863 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b77 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e79 : ℝ := e76 - e78
lemma b79 : Encl e79 (690007777 / 100000000000 : ℝ) (431254861 / 62500000000 : ℝ) := by
  exact Encl.sub b76 b78 (by norm_num) (by norm_num)

def e80 : ℝ := e43 * e32
lemma b80 : Encl e80 (39161181661 / 800000000 : ℝ) (979029541527 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e81 : ℝ := e12 / e80
lemma b81 : Encl e81 (4161637999 / 1000000000000 : ℝ) (4161638001 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b12 b80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e82 : ℝ := e79 - e81
lemma b82 : Encl e82 (2738439769 / 1000000000000 : ℝ) (2738439777 / 1000000000000 : ℝ) := by
  exact Encl.sub b79 b81 (by norm_num) (by norm_num)

def e83 : ℝ := e67 - e82
lemma b83 : Encl e83 (25450440101 / 1000000000000 : ℝ) (12725220059 / 500000000000 : ℝ) := by
  exact Encl.sub b67 b82 (by norm_num) (by norm_num)

def e84 : ℝ := e83 / e11
lemma b84 : Encl e84 (39766312657 / 1000000000000 : ℝ) (7953262537 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b83 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e85 : ℝ := e47 + e84
lemma b85 : Encl e85 (-10132971337 / 20000000000 : ℝ) (-506648566757 / 1000000000000 : ℝ) := by
  exact Encl.add b47 b84 (by norm_num) (by norm_num)

def e86 : ℝ := e13 + e4
lemma b86 : Encl e86 (356506247863 / 250000000000 : ℝ) (713012495727 / 500000000000 : ℝ) := by
  exact Encl.add b13 b4 (by norm_num) (by norm_num)

def e87 : ℝ := e86 / e23
lemma b87 : Encl e87 (356506247863 / 500000000000 : ℝ) (713012495727 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b86 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e88 : ℝ := e13 / e11
lemma b88 : Encl e88 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e89 : ℝ := Real.sqrt e0
lemma b89 : Encl e89 (354490770181 / 200000000000 : ℝ) (886226925453 / 500000000000 : ℝ) := by
  exact Encl.sqrt b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e90 : ℝ := e89 * e88
lemma b90 : Encl e90 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b88 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e91 : ℝ := e0 / e17
lemma b91 : Encl e91 (785398163397 / 1000000000000 : ℝ) (392699081699 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e92 : ℝ := e88 ^ 2
lemma b92 : Encl e92 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b88 (by norm_num) 2 (by norm_num) (by norm_num)

def e93 : ℝ := e91 * e92
lemma b93 : Encl e93 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e94 : ℝ := e5 + e93
lemma b94 : Encl e94 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b93 (by norm_num) (by norm_num)

def e95 : ℝ := Real.sqrt e94
lemma b95 : Encl e95 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b94 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e96 : ℝ := e90 * e95
lemma b96 : Encl e96 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b90 b95 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e97 : ℝ := e0 / e23
lemma b97 : Encl e97 (785398163397 / 500000000000 : ℝ) (314159265359 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e98 : ℝ := e97 * e92
lemma b98 : Encl e98 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e99 : ℝ := e96 - e98
lemma b99 : Encl e99 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b96 b98 (by norm_num) (by norm_num)

def e100 : ℝ := e87 * e99
lemma b100 : Encl e100 (97210713871 / 200000000000 : ℝ) (486053569373 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b87 b99 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e101 : ℝ := e87 / e11
lemma b101 : Encl e101 (1114082024571 / 1000000000000 : ℝ) (557041012287 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e102 : ℝ := e89 * e101
lemma b102 : Encl e102 (987329487337 / 500000000000 : ℝ) (987329487341 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b101 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e103 : ℝ := e101 ^ 2
lemma b103 : Encl e103 (38786836171 / 31250000000 : ℝ) (1241178757479 / 1000000000000 : ℝ) := by
  exact Encl.pow b101 (by norm_num) 2 (by norm_num) (by norm_num)

def e104 : ℝ := e91 * e103
lemma b104 : Encl e104 (194963903313 / 200000000000 : ℝ) (974819516573 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e105 : ℝ := e5 + e104
lemma b105 : Encl e105 (394963903313 / 200000000000 : ℝ) (1974819516573 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b104 (by norm_num) (by norm_num)

def e106 : ℝ := Real.sqrt e105
lemma b106 : Encl e106 (1405282717663 / 1000000000000 : ℝ) (1405282717667 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e107 : ℝ := e102 * e106
lemma b107 : Encl e107 (2774954130387 / 1000000000000 : ℝ) (2774954130407 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b102 b106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e108 : ℝ := e97 * e103
lemma b108 : Encl e108 (1949639033131 / 1000000000000 : ℝ) (243704879143 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e109 : ℝ := e107 - e108
lemma b109 : Encl e109 (825315097243 / 1000000000000 : ℝ) (206328774319 / 250000000000 : ℝ) := by
  exact Encl.sub b107 b108 (by norm_num) (by norm_num)

def e110 : ℝ := e13 * e109
lemma b110 : Encl e110 (180034925623 / 500000000000 : ℝ) (360069851263 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b13 b109 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e111 : ℝ := e100 - e110
lemma b111 : Encl e111 (31495929523 / 250000000000 : ℝ) (125983718127 / 1000000000000 : ℝ) := by
  exact Encl.sub b100 b110 (by norm_num) (by norm_num)

def e112 : ℝ := e87 ^ 2
lemma b112 : Encl e112 (508386819061 / 1000000000000 : ℝ) (508386819063 / 1000000000000 : ℝ) := by
  exact Encl.pow b87 (by norm_num) 2 (by norm_num) (by norm_num)

def e113 : ℝ := e8 * e112
lemma b113 : Encl e113 (498219082679 / 1000000000000 : ℝ) (249109541341 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b112 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e114 : ℝ := e5 - e113
lemma b114 : Encl e114 (250890458659 / 500000000000 : ℝ) (501780917321 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b113 (by norm_num) (by norm_num)

def e115 : ℝ := e5 - e112
lemma b115 : Encl e115 (491613180937 / 1000000000000 : ℝ) (491613180939 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b112 (by norm_num) (by norm_num)

def e116 : ℝ := Real.sqrt e115
lemma b116 : Encl e116 (175287831319 / 250000000000 : ℝ) (350575662639 / 500000000000 : ℝ) := by
  exact Encl.sqrt b115 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e117 : ℝ := e114 / e116
lemma b117 : Encl e117 (178913202909 / 250000000000 : ℝ) (178913202911 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b114 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e118 : ℝ := e5 - e117
lemma b118 : Encl e118 (71086797089 / 250000000000 : ℝ) (71086797091 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b117 (by norm_num) (by norm_num)

def e119 : ℝ := e8 * e48
lemma b119 : Encl e119 (37306972819 / 200000000000 : ℝ) (93267432049 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e120 : ℝ := e5 - e119
lemma b120 : Encl e120 (406732567951 / 500000000000 : ℝ) (162693027181 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b119 (by norm_num) (by norm_num)

def e121 : ℝ := e120 / e50
lemma b121 : Encl e121 (452020427843 / 500000000000 : ℝ) (226010213923 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b120 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e122 : ℝ := e5 - e121
lemma b122 : Encl e122 (23989786077 / 250000000000 : ℝ) (47979572157 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b121 (by norm_num) (by norm_num)

def e123 : ℝ := e118 - e122
lemma b123 : Encl e123 (94194022021 / 500000000000 : ℝ) (23548505507 / 125000000000 : ℝ) := by
  exact Encl.sub b118 b122 (by norm_num) (by norm_num)

def e124 : ℝ := e111 * e123
lemma b124 : Encl e124 (2966728279 / 125000000000 : ℝ) (23733826241 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b111 b123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e125 : ℝ := e109 - e99
lemma b125 : Encl e125 (28724996683 / 200000000000 : ℝ) (143624983471 / 1000000000000 : ℝ) := by
  exact Encl.sub b109 b99 (by norm_num) (by norm_num)

def e126 : ℝ := e5 + e116
lemma b126 : Encl e126 (425287831319 / 250000000000 : ℝ) (850575662639 / 500000000000 : ℝ) := by
  exact Encl.add b5 b116 (by norm_num) (by norm_num)

def e127 : ℝ := e87 / e126
lemma b127 : Encl e127 (13097976741 / 31250000000 : ℝ) (209567627857 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b126 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e128 : ℝ := e127 ^ 2
lemma b128 : Encl e128 (8783718129 / 50000000000 : ℝ) (175674362583 / 1000000000000 : ℝ) := by
  exact Encl.pow b127 (by norm_num) 2 (by norm_num) (by norm_num)

def e129 : ℝ := e5 + e128
lemma b129 : Encl e129 (58783718129 / 50000000000 : ℝ) (1175674362583 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b128 (by norm_num) (by norm_num)

def e130 : ℝ := Real.sqrt e129
lemma b130 : Encl e130 (542142592539 / 500000000000 : ℝ) (27107129627 / 25000000000 : ℝ) := by
  exact Encl.sqrt b129 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e131 : ℝ := e5 + e130
lemma b131 : Encl e131 (1042142592539 / 500000000000 : ℝ) (52107129627 / 25000000000 : ℝ) := by
  exact Encl.add b5 b130 (by norm_num) (by norm_num)

def e132 : ℝ := e127 / e131
lemma b132 : Encl e132 (201093045573 / 1000000000000 : ℝ) (8043721823 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b127 b131 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e133 : ℝ := Real.arcsin e87
lemma b133 : Encl e133 (793785375783 / 1000000000000 : ℝ) (793785375791 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e87) (a := (201093045573 / 1000000000000 : ℝ)) (b := (8043721823 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (356506247863 / 500000000000 : ℝ) by norm_num).trans b87.1
        exact b87.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e87) (201093045573 / 1000000000000 : ℝ) (8043721823 / 40000000000 : ℝ) from b132) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e134 : ℝ := e59 * e133
lemma b134 : Encl e134 (404830541649 / 1000000000000 : ℝ) (202415270827 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b133 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e135 : ℝ := e61 * e87
lemma b135 : Encl e135 (69875224581 / 200000000000 : ℝ) (349376122907 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b87 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e136 : ℝ := e135 * e116
lemma b136 : Encl e136 (122482765797 / 500000000000 : ℝ) (244965531597 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b135 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e137 : ℝ := e134 - e136
lemma b137 : Encl e137 (39966252513 / 250000000000 : ℝ) (7993250503 / 50000000000 : ℝ) := by
  exact Encl.sub b134 b136 (by norm_num) (by norm_num)

def e138 : ℝ := e43 * e116
lemma b138 : Encl e138 (175287831319 / 5000000000 : ℝ) (350575662639 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e139 : ℝ := e87 / e138
lemma b139 : Encl e139 (20338334109 / 1000000000000 : ℝ) (2033833411 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e140 : ℝ := e137 - e139
lemma b140 : Encl e140 (69763337971 / 500000000000 : ℝ) (139526675951 / 1000000000000 : ℝ) := by
  exact Encl.sub b137 b139 (by norm_num) (by norm_num)

def e141 : ℝ := e140 - e67
lemma b141 : Encl e141 (22267559211 / 200000000000 : ℝ) (111337796073 / 1000000000000 : ℝ) := by
  exact Encl.sub b140 b67 (by norm_num) (by norm_num)

def e142 : ℝ := e125 * e141
lemma b142 : Encl e142 (15990889111 / 1000000000000 : ℝ) (15990889121 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b125 b141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e143 : ℝ := e124 + e142
lemma b143 : Encl e143 (39724715343 / 1000000000000 : ℝ) (19862357681 / 500000000000 : ℝ) := by
  exact Encl.add b124 b142 (by norm_num) (by norm_num)

def e144 : ℝ := e87 - e13
lemma b144 : Encl e144 (276730822883 / 1000000000000 : ℝ) (55346164577 / 200000000000 : ℝ) := by
  exact Encl.sub b87 b13 (by norm_num) (by norm_num)

def e145 : ℝ := e143 / e144
lemma b145 : Encl e145 (71775010331 / 500000000000 : ℝ) (35887505183 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b143 b144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e146 : ℝ := e85 + e145
lemma b146 : Encl e146 (-90774636547 / 250000000000 : ℝ) (-14523941841 / 40000000000 : ℝ) := by
  exact Encl.add b85 b145 (by norm_num) (by norm_num)

def e147 : ℝ := e4 * e109
lemma b147 : Encl e147 (204212525811 / 250000000000 : ℝ) (408425051639 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b109 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e148 : ℝ := e4 / e11
lemma b148 : Encl e148 (48327310479 / 31250000000 : ℝ) (154647393533 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e149 : ℝ := e89 * e148
lemma b149 : Encl e149 (685263420499 / 250000000000 : ℝ) (1370526841001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b148 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e150 : ℝ := e148 ^ 2
lemma b150 : Encl e150 (298947704081 / 125000000000 : ℝ) (149473852041 / 62500000000 : ℝ) := by
  exact Encl.pow b148 (by norm_num) 2 (by norm_num) (by norm_num)

def e151 : ℝ := e91 * e150
lemma b151 : Encl e151 (375668764379 / 200000000000 : ℝ) (375668764381 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e152 : ℝ := e5 + e151
lemma b152 : Encl e152 (575668764379 / 200000000000 : ℝ) (575668764381 / 200000000000 : ℝ) := by
  exact Encl.add b5 b151 (by norm_num) (by norm_num)

def e153 : ℝ := Real.sqrt e152
lemma b153 : Encl e153 (848284124261 / 500000000000 : ℝ) (848284124263 / 500000000000 : ℝ) := by
  exact Encl.sqrt b152 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e154 : ℝ := e149 * e153
lemma b154 : Encl e154 (290649040273 / 62500000000 : ℝ) (465038464439 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b149 b153 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e155 : ℝ := e97 * e150
lemma b155 : Encl e155 (3756687643791 / 1000000000000 : ℝ) (3756687643807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e156 : ℝ := e154 - e155
lemma b156 : Encl e156 (893697000561 / 1000000000000 : ℝ) (893697000599 / 1000000000000 : ℝ) := by
  exact Encl.sub b154 b155 (by norm_num) (by norm_num)

def e157 : ℝ := e87 * e156
lemma b157 : Encl e157 (79652141099 / 125000000000 : ℝ) (637217128821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b87 b156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e158 : ℝ := e147 - e157
lemma b158 : Encl e158 (179632974423 / 1000000000000 : ℝ) (89816487243 / 500000000000 : ℝ) := by
  exact Encl.sub b147 b157 (by norm_num) (by norm_num)

def e159 : ℝ := e4 ^ 2
lemma b159 : Encl e159 (979591836733 / 1000000000000 : ℝ) (15306122449 / 15625000000 : ℝ) := by
  exact Encl.pow b4 (by norm_num) 2 (by norm_num) (by norm_num)

def e160 : ℝ := e8 * e159
lemma b160 : Encl e160 (479999999999 / 500000000000 : ℝ) (480000000001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b159 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e161 : ℝ := e5 - e160
lemma b161 : Encl e161 (19999999999 / 500000000000 : ℝ) (20000000001 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b160 (by norm_num) (by norm_num)

def e162 : ℝ := e5 - e159
lemma b162 : Encl e162 (318877551 / 15625000000 : ℝ) (20408163267 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b159 (by norm_num) (by norm_num)

def e163 : ℝ := Real.sqrt e162
lemma b163 : Encl e163 (35714285713 / 250000000000 : ℝ) (8928571429 / 62500000000 : ℝ) := by
  exact Encl.sqrt b162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e164 : ℝ := e161 / e163
lemma b164 : Encl e164 (69999999993 / 250000000000 : ℝ) (11200000001 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b161 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e165 : ℝ := e5 - e164
lemma b165 : Encl e165 (28799999999 / 40000000000 : ℝ) (180000000007 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b164 (by norm_num) (by norm_num)

def e166 : ℝ := e165 - e118
lemma b166 : Encl e166 (435652811611 / 1000000000000 : ℝ) (54456601459 / 125000000000 : ℝ) := by
  exact Encl.sub b165 b118 (by norm_num) (by norm_num)

def e167 : ℝ := e158 * e166
lemma b167 : Encl e167 (15651522073 / 200000000000 : ℝ) (19564402601 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b158 b166 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e168 : ℝ := e156 - e109
lemma b168 : Encl e168 (13676380657 / 200000000000 : ℝ) (17095475839 / 250000000000 : ℝ) := by
  exact Encl.sub b156 b109 (by norm_num) (by norm_num)

def e169 : ℝ := e5 + e163
lemma b169 : Encl e169 (285714285713 / 250000000000 : ℝ) (71428571429 / 62500000000 : ℝ) := by
  exact Encl.add b5 b163 (by norm_num) (by norm_num)

def e170 : ℝ := e4 / e169
lemma b170 : Encl e170 (433012701889 / 500000000000 : ℝ) (866025403789 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b169 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e171 : ℝ := e170 ^ 2
lemma b171 : Encl e171 (187499999997 / 250000000000 : ℝ) (93750000001 / 125000000000 : ℝ) := by
  exact Encl.pow b170 (by norm_num) 2 (by norm_num) (by norm_num)

def e172 : ℝ := e5 + e171
lemma b172 : Encl e172 (437499999997 / 250000000000 : ℝ) (218750000001 / 125000000000 : ℝ) := by
  exact Encl.add b5 b171 (by norm_num) (by norm_num)

def e173 : ℝ := Real.sqrt e172
lemma b173 : Encl e173 (1322875655527 / 1000000000000 : ℝ) (82679728471 / 62500000000 : ℝ) := by
  exact Encl.sqrt b172 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e174 : ℝ := e5 + e173
lemma b174 : Encl e174 (2322875655527 / 1000000000000 : ℝ) (145179728471 / 62500000000 : ℝ) := by
  exact Encl.add b5 b173 (by norm_num) (by norm_num)

def e175 : ℝ := e170 / e174
lemma b175 : Encl e175 (372824693269 / 1000000000000 : ℝ) (93206173319 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b170 b174 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e176 : ℝ := Real.arcsin e4
lemma b176 : Encl e176 (713724378853 / 500000000000 : ℝ) (1427448757923 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e4) (a := (372824693269 / 1000000000000 : ℝ)) (b := (93206173319 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (98974331861 / 100000000000 : ℝ) by norm_num).trans b4.1
        exact b4.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e4) (372824693269 / 1000000000000 : ℝ) (93206173319 / 250000000000 : ℝ) from b175) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e177 : ℝ := e59 * e176
lemma b177 : Encl e177 (72799886643 / 100000000000 : ℝ) (727998866541 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b176 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e178 : ℝ := e61 * e4
lemma b178 : Encl e178 (242487113059 / 500000000000 : ℝ) (12124355653 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e179 : ℝ := e178 * e163
lemma b179 : Encl e179 (692820323 / 10000000000 : ℝ) (69282032307 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b178 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e180 : ℝ := e177 - e179
lemma b180 : Encl e180 (658716834123 / 1000000000000 : ℝ) (658716834241 / 1000000000000 : ℝ) := by
  exact Encl.sub b177 b179 (by norm_num) (by norm_num)

def e181 : ℝ := e43 * e163
lemma b181 : Encl e181 (35714285713 / 5000000000 : ℝ) (8928571429 / 1250000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e182 : ℝ := e4 / e181
lemma b182 : Encl e182 (69282032299 / 500000000000 : ℝ) (138564064611 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b181 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e183 : ℝ := e180 - e182
lemma b183 : Encl e183 (65019096189 / 125000000000 : ℝ) (520152769643 / 1000000000000 : ℝ) := by
  exact Encl.sub b180 b182 (by norm_num) (by norm_num)

def e184 : ℝ := e183 - e140
lemma b184 : Encl e184 (380626093561 / 1000000000000 : ℝ) (380626093701 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b140 (by norm_num) (by norm_num)

def e185 : ℝ := e168 * e184
lemma b185 : Encl e185 (26027936717 / 1000000000000 : ℝ) (5205587351 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b168 b184 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e186 : ℝ := e167 + e185
lemma b186 : Encl e186 (52142773541 / 500000000000 : ℝ) (104285547159 / 1000000000000 : ℝ) := by
  exact Encl.add b167 b185 (by norm_num) (by norm_num)

def e187 : ℝ := e4 - e87
lemma b187 : Encl e187 (276730822883 / 1000000000000 : ℝ) (55346164577 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b87 (by norm_num) (by norm_num)

def e188 : ℝ := e186 / e187
lemma b188 : Encl e188 (188424162503 / 500000000000 : ℝ) (47106040661 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b186 b187 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e189 : ℝ := e146 + e188
lemma b189 : Encl e189 (6874889409 / 500000000000 : ℝ) (13749779263 / 1000000000000 : ℝ) := by
  exact Encl.add b146 b188 (by norm_num) (by norm_num)

def e190 : ℝ := (37 / 50 : ℝ)
lemma b190 : Encl e190 (37 / 50 : ℝ) (37 / 50 : ℝ) := by
  exact Encl.exact (37 / 50 : ℝ)

def e191 : ℝ := e190 / e0
lemma b191 : Encl e191 (3680458059 / 15625000000 : ℝ) (235549315777 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b190 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e192 : ℝ := e190 * e7
lemma b192 : Encl e192 (504450684223 / 1000000000000 : ℝ) (20178027369 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b190 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e193 : ℝ := e8 * e190
lemma b193 : Encl e193 (1813 / 2500 : ℝ) (1813 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e194 : ℝ := e193 / e0
lemma b194 : Encl e194 (11541916473 / 50000000000 : ℝ) (230838329461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b193 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e195 : ℝ := e190 ^ 2
lemma b195 : Encl e195 (1369 / 2500 : ℝ) (1369 / 2500 : ℝ) := by
  exact Encl.pow b190 (by norm_num) 2 (by norm_num) (by norm_num)

def e196 : ℝ := e17 * e195
lemma b196 : Encl e196 (1369 / 625 : ℝ) (1369 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e197 : ℝ := e196 / e0
lemma b197 : Encl e197 (87153246837 / 125000000000 : ℝ) (697225974697 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b196 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e198 : ℝ := e5 + e197
lemma b198 : Encl e198 (212153246837 / 125000000000 : ℝ) (1697225974697 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b197 (by norm_num) (by norm_num)

def e199 : ℝ := Real.sqrt e198
lemma b199 : Encl e199 (52111050263 / 40000000000 : ℝ) (20355879009 / 15625000000 : ℝ) := by
  exact Encl.sqrt b198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e200 : ℝ := e5 + e199
lemma b200 : Encl e200 (92111050263 / 40000000000 : ℝ) (35980879009 / 15625000000 : ℝ) := by
  exact Encl.add b5 b199 (by norm_num) (by norm_num)

def e201 : ℝ := e23 / e200
lemma b201 : Encl e201 (868516858417 / 1000000000000 : ℝ) (434258429209 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b200 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e202 : ℝ := e9 * e201
lemma b202 : Encl e202 (60796180089 / 250000000000 : ℝ) (121592360179 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b201 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e203 : ℝ := e194 + e202
lemma b203 : Encl e203 (59252881227 / 125000000000 : ℝ) (474023049819 / 1000000000000 : ℝ) := by
  exact Encl.add b194 b202 (by norm_num) (by norm_num)

def e204 : ℝ := e203 - e5
lemma b204 : Encl e204 (-65747118773 / 125000000000 : ℝ) (-525976950181 / 1000000000000 : ℝ) := by
  exact Encl.sub b203 b5 (by norm_num) (by norm_num)

def e205 : ℝ := e0 / e195
lemma b205 : Encl e205 (2868510457989 / 500000000000 : ℝ) (5737020915979 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e206 : ℝ := e191 ^ 2
lemma b206 : Encl e206 (27741740081 / 500000000000 : ℝ) (13870870041 / 250000000000 : ℝ) := by
  exact Encl.pow b191 (by norm_num) 2 (by norm_num) (by norm_num)

def e207 : ℝ := e5 - e206
lemma b207 : Encl e207 (236129129959 / 250000000000 : ℝ) (472258259919 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b206 (by norm_num) (by norm_num)

def e208 : ℝ := Real.sqrt e207
lemma b208 : Encl e208 (971862397583 / 1000000000000 : ℝ) (194372479517 / 200000000000 : ℝ) := by
  exact Encl.sqrt b207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e209 : ℝ := e29 - e208
lemma b209 : Encl e209 (-305195730919 / 1000000000000 : ℝ) (-76298932729 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b208 (by norm_num) (by norm_num)

def e210 : ℝ := e208 ^ 3
lemma b210 : Encl e210 (229485022381 / 250000000000 : ℝ) (917940089531 / 1000000000000 : ℝ) := by
  exact Encl.pow b208 (by norm_num) 3 (by norm_num) (by norm_num)

def e211 : ℝ := e210 / e35
lemma b211 : Encl e211 (305980029841 / 1000000000000 : ℝ) (76495007461 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b210 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e212 : ℝ := e209 + e211
lemma b212 : Encl e212 (392149461 / 500000000000 : ℝ) (49018683 / 62500000000 : ℝ) := by
  exact Encl.add b209 b211 (by norm_num) (by norm_num)

def e213 : ℝ := e8 * e212
lemma b213 : Encl e213 (768612943 / 1000000000000 : ℝ) (15372259 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b212 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e214 : ℝ := e206 / e208
lemma b214 : Encl e214 (57089851711 / 1000000000000 : ℝ) (28544925857 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b206 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e215 : ℝ := e214 - e23
lemma b215 : Encl e215 (-1942910148289 / 1000000000000 : ℝ) (-971455074143 / 500000000000 : ℝ) := by
  exact Encl.sub b214 b23 (by norm_num) (by norm_num)

def e216 : ℝ := e23 * e208
lemma b216 : Encl e216 (971862397583 / 500000000000 : ℝ) (194372479517 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e217 : ℝ := e215 + e216
lemma b217 : Encl e217 (814646877 / 1000000000000 : ℝ) (203661721 / 250000000000 : ℝ) := by
  exact Encl.add b215 b216 (by norm_num) (by norm_num)

def e218 : ℝ := e217 / e43
lemma b218 : Encl e218 (16292937 / 1000000000000 : ℝ) (8146469 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b217 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e219 : ℝ := e213 - e218
lemma b219 : Encl e219 (150464001 / 200000000000 : ℝ) (752320013 / 1000000000000 : ℝ) := by
  exact Encl.sub b213 b218 (by norm_num) (by norm_num)

def e220 : ℝ := e205 * e219
lemma b220 : Encl e220 (1079018901 / 250000000000 : ℝ) (4316075651 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b205 b219 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e221 : ℝ := e204 + e220
lemma b221 : Encl e221 (-26083043729 / 50000000000 : ℝ) (-52166087453 / 100000000000 : ℝ) := by
  exact Encl.add b204 b220 (by norm_num) (by norm_num)

def e222 : ℝ := e192 ^ 2
lemma b222 : Encl e222 (254470492813 / 1000000000000 : ℝ) (15904405801 / 62500000000 : ℝ) := by
  exact Encl.pow b192 (by norm_num) 2 (by norm_num) (by norm_num)

def e223 : ℝ := e5 - e222
lemma b223 : Encl e223 (46595594199 / 62500000000 : ℝ) (745529507187 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b222 (by norm_num) (by norm_num)

def e224 : ℝ := Real.sqrt e223
lemma b224 : Encl e224 (431720252937 / 500000000000 : ℝ) (215860126469 / 250000000000 : ℝ) := by
  exact Encl.sqrt b223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e225 : ℝ := e5 + e224
lemma b225 : Encl e225 (931720252937 / 500000000000 : ℝ) (465860126469 / 250000000000 : ℝ) := by
  exact Encl.add b5 b224 (by norm_num) (by norm_num)

def e226 : ℝ := e192 / e225
lemma b226 : Encl e226 (270709304983 / 1000000000000 : ℝ) (54141860997 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e227 : ℝ := e226 ^ 2
lemma b227 : Encl e227 (18320881951 / 250000000000 : ℝ) (36641763903 / 500000000000 : ℝ) := by
  exact Encl.pow b226 (by norm_num) 2 (by norm_num) (by norm_num)

def e228 : ℝ := e5 + e227
lemma b228 : Encl e228 (268320881951 / 250000000000 : ℝ) (536641763903 / 500000000000 : ℝ) := by
  exact Encl.add b5 b227 (by norm_num) (by norm_num)

def e229 : ℝ := Real.sqrt e228
lemma b229 : Encl e229 (517996990291 / 500000000000 : ℝ) (129499247573 / 125000000000 : ℝ) := by
  exact Encl.sqrt b228 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e230 : ℝ := e5 + e229
lemma b230 : Encl e230 (1017996990291 / 500000000000 : ℝ) (254499247573 / 125000000000 : ℝ) := by
  exact Encl.add b5 b229 (by norm_num) (by norm_num)

def e231 : ℝ := e226 / e230
lemma b231 : Encl e231 (132961741323 / 1000000000000 : ℝ) (5318469653 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b226 b230 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e232 : ℝ := Real.arcsin e192
lemma b232 : Encl e232 (264372826437 / 500000000000 : ℝ) (528745652883 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e192) (a := (132961741323 / 1000000000000 : ℝ)) (b := (5318469653 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (504450684223 / 1000000000000 : ℝ) by norm_num).trans b192.1
        exact b192.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e192) (132961741323 / 1000000000000 : ℝ) (5318469653 / 40000000000 : ℝ) from b231) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e233 : ℝ := e59 * e232
lemma b233 : Encl e233 (53932056593 / 200000000000 : ℝ) (269660282971 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e234 : ℝ := e61 * e192
lemma b234 : Encl e234 (247180835269 / 1000000000000 : ℝ) (247180835271 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e235 : ℝ := e234 * e224
lemma b235 : Encl e235 (213425945447 / 1000000000000 : ℝ) (4268518909 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b234 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e236 : ℝ := e233 - e235
lemma b236 : Encl e236 (11246867503 / 200000000000 : ℝ) (14058584381 / 250000000000 : ℝ) := by
  exact Encl.sub b233 b235 (by norm_num) (by norm_num)

def e237 : ℝ := e43 * e224
lemma b237 : Encl e237 (431720252937 / 10000000000 : ℝ) (215860126469 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e238 : ℝ := e192 / e237
lemma b238 : Encl e238 (2921166431 / 250000000000 : ℝ) (467386629 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b237 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e239 : ℝ := e236 - e238
lemma b239 : Encl e239 (4454967179 / 100000000000 : ℝ) (222748359 / 5000000000 : ℝ) := by
  exact Encl.sub b236 b238 (by norm_num) (by norm_num)

def e240 : ℝ := e5 + e208
lemma b240 : Encl e240 (1971862397583 / 1000000000000 : ℝ) (394372479517 / 200000000000 : ℝ) := by
  exact Encl.add b5 b208 (by norm_num) (by norm_num)

def e241 : ℝ := e191 / e240
lemma b241 : Encl e241 (59727625027 / 500000000000 : ℝ) (23891050011 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b191 b240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e242 : ℝ := e241 ^ 2
lemma b242 : Encl e242 (2853911353 / 200000000000 : ℝ) (7134778383 / 500000000000 : ℝ) := by
  exact Encl.pow b241 (by norm_num) 2 (by norm_num) (by norm_num)

def e243 : ℝ := e5 + e242
lemma b243 : Encl e243 (202853911353 / 200000000000 : ℝ) (507134778383 / 500000000000 : ℝ) := by
  exact Encl.add b5 b242 (by norm_num) (by norm_num)

def e244 : ℝ := Real.sqrt e243
lemma b244 : Encl e244 (201421901169 / 200000000000 : ℝ) (1007109505847 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b243 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e245 : ℝ := e5 + e244
lemma b245 : Encl e245 (401421901169 / 200000000000 : ℝ) (2007109505847 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b244 (by norm_num) (by norm_num)

def e246 : ℝ := e241 / e245
lemma b246 : Encl e246 (29758030069 / 500000000000 : ℝ) (59516060139 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b241 b245 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e247 : ℝ := Real.arcsin e191
lemma b247 : Encl e247 (59445937279 / 250000000000 : ℝ) (237783749121 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e191) (a := (29758030069 / 500000000000 : ℝ)) (b := (59516060139 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (3680458059 / 15625000000 : ℝ) by norm_num).trans b191.1
        exact b191.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e191) (29758030069 / 500000000000 : ℝ) (59516060139 / 1000000000000 : ℝ) from b246) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e248 : ℝ := e59 * e247
lemma b248 : Encl e248 (121269712049 / 1000000000000 : ℝ) (30317428013 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e249 : ℝ := e61 * e191
lemma b249 : Encl e249 (11541916473 / 100000000000 : ℝ) (115419164731 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b191 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e250 : ℝ := e249 * e208
lemma b250 : Encl e250 (112171546161 / 1000000000000 : ℝ) (112171546163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b249 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e251 : ℝ := e248 - e250
lemma b251 : Encl e251 (4549082943 / 500000000000 : ℝ) (9098165891 / 1000000000000 : ℝ) := by
  exact Encl.sub b248 b250 (by norm_num) (by norm_num)

def e252 : ℝ := e43 * e208
lemma b252 : Encl e252 (971862397583 / 20000000000 : ℝ) (194372479517 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e253 : ℝ := e191 / e252
lemma b253 : Encl e253 (969475993 / 200000000000 : ℝ) (2423689983 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b191 b252 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e254 : ℝ := e251 - e253
lemma b254 : Encl e254 (6641853 / 1562500000 : ℝ) (2125392963 / 500000000000 : ℝ) := by
  exact Encl.sub b251 b253 (by norm_num) (by norm_num)

def e255 : ℝ := e239 - e254
lemma b255 : Encl e255 (5037360733 / 125000000000 : ℝ) (1007472147 / 25000000000 : ℝ) := by
  exact Encl.sub b239 b254 (by norm_num) (by norm_num)

def e256 : ℝ := e255 / e190
lemma b256 : Encl e256 (5445795387 / 100000000000 : ℝ) (13614488473 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b255 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e257 : ℝ := e221 + e256
lemma b257 : Encl e257 (-46720292071 / 100000000000 : ℝ) (-233601460319 / 500000000000 : ℝ) := by
  exact Encl.add b221 b256 (by norm_num) (by norm_num)

def e258 : ℝ := e192 + e4
lemma b258 : Encl e258 (1494194002833 / 1000000000000 : ℝ) (373548500709 / 250000000000 : ℝ) := by
  exact Encl.add b192 b4 (by norm_num) (by norm_num)

def e259 : ℝ := e258 / e23
lemma b259 : Encl e259 (93387125177 / 125000000000 : ℝ) (373548500709 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b258 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e260 : ℝ := e192 / e190
lemma b260 : Encl e260 (340845056907 / 500000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e261 : ℝ := e89 * e260
lemma b261 : Encl e261 (1208264267353 / 1000000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b260 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e262 : ℝ := e260 ^ 2
lemma b262 : Encl e262 (464701411271 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b260 (by norm_num) 2 (by norm_num) (by norm_num)

def e263 : ℝ := e91 * e262
lemma b263 : Encl e263 (18248781747 / 50000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e264 : ℝ := e5 + e263
lemma b264 : Encl e264 (68248781747 / 50000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b263 (by norm_num) (by norm_num)

def e265 : ℝ := Real.sqrt e264
lemma b265 : Encl e265 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e266 : ℝ := e261 * e265
lemma b266 : Encl e266 (282328276739 / 200000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b261 b265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e267 : ℝ := e97 * e262
lemma b267 : Encl e267 (18248781747 / 25000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e268 : ℝ := e266 - e267
lemma b268 : Encl e268 (681690113803 / 1000000000000 : ℝ) (681690113831 / 1000000000000 : ℝ) := by
  exact Encl.sub b266 b267 (by norm_num) (by norm_num)

def e269 : ℝ := e259 * e268
lemma b269 : Encl e269 (509288639917 / 1000000000000 : ℝ) (25464431997 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b259 b268 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e270 : ℝ := e259 / e190
lemma b270 : Encl e270 (504795271227 / 500000000000 : ℝ) (1009590542457 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e271 : ℝ := e89 * e270
lemma b271 : Encl e271 (1789452644809 / 1000000000000 : ℝ) (1789452644817 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b270 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e272 : ℝ := e270 ^ 2
lemma b272 : Encl e272 (254818265853 / 250000000000 : ℝ) (1019273063419 / 1000000000000 : ℝ) := by
  exact Encl.pow b270 (by norm_num) 2 (by norm_num) (by norm_num)

def e273 : ℝ := e91 * e272
lemma b273 : Encl e273 (800535192003 / 1000000000000 : ℝ) (800535192011 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e274 : ℝ := e5 + e273
lemma b274 : Encl e274 (1800535192003 / 1000000000000 : ℝ) (1800535192011 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b273 (by norm_num) (by norm_num)

def e275 : ℝ := Real.sqrt e274
lemma b275 : Encl e275 (1341840225959 / 1000000000000 : ℝ) (1341840225963 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e276 : ℝ := e271 * e275
lemma b276 : Encl e276 (2401159541253 / 1000000000000 : ℝ) (300144942659 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b271 b275 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e277 : ℝ := e97 * e272
lemma b277 : Encl e277 (1601070384007 / 1000000000000 : ℝ) (80053519201 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e278 : ℝ := e276 - e277
lemma b278 : Encl e278 (800089157233 / 1000000000000 : ℝ) (160017831453 / 200000000000 : ℝ) := by
  exact Encl.sub b276 b277 (by norm_num) (by norm_num)

def e279 : ℝ := e192 * e278
lemma b279 : Encl e279 (80721104561 / 200000000000 : ℝ) (50450690353 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b192 b278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e280 : ℝ := e269 - e279
lemma b280 : Encl e280 (105683117093 / 1000000000000 : ℝ) (21136623427 / 200000000000 : ℝ) := by
  exact Encl.sub b269 b279 (by norm_num) (by norm_num)

def e281 : ℝ := e259 ^ 2
lemma b281 : Encl e281 (139538482381 / 250000000000 : ℝ) (69769241191 / 125000000000 : ℝ) := by
  exact Encl.pow b259 (by norm_num) 2 (by norm_num) (by norm_num)

def e282 : ℝ := e8 * e281
lemma b282 : Encl e282 (546990850933 / 1000000000000 : ℝ) (273495425469 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e283 : ℝ := e5 - e282
lemma b283 : Encl e283 (226504574531 / 500000000000 : ℝ) (453009149067 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b282 (by norm_num) (by norm_num)

def e284 : ℝ := e5 - e281
lemma b284 : Encl e284 (55230758809 / 125000000000 : ℝ) (110461517619 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b281 (by norm_num) (by norm_num)

def e285 : ℝ := Real.sqrt e284
lemma b285 : Encl e285 (664715029521 / 1000000000000 : ℝ) (26588601181 / 40000000000 : ℝ) := by
  exact Encl.sqrt b284 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e286 : ℝ := e283 / e285
lemma b286 : Encl e286 (681508810453 / 1000000000000 : ℝ) (136301762093 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b283 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e287 : ℝ := e5 - e286
lemma b287 : Encl e287 (63698237907 / 200000000000 : ℝ) (318491189547 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b286 (by norm_num) (by norm_num)

def e288 : ℝ := e8 * e222
lemma b288 : Encl e288 (62345270739 / 250000000000 : ℝ) (3117263537 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b222 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI

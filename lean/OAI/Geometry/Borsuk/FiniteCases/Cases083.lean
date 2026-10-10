import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases002
import OAI.Geometry.Borsuk.FiniteCases.Cases033
import OAI.Geometry.Borsuk.FiniteCases.Cases082

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31263 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → ¬ Q {0, 1, 2, 7} → T {6, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {3, 6, 8, 9} → T {3, 4, 5} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  classical
  intro a311 n125 a118 n127 n126 n184 n240 n314 a86 n275 n315
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u2_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u3_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1497 h a311 n184 n240 n275 hv n314 n315
  have u4_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u1_93 a118
  have u5_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2255 h hv a86 u1_93 u2_94
  have u6_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u3_305 hv
  have u7_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c4 h u0_121 u4_122 hv u5_124 n125 n126 n127
  exact c2087 h u7_123 u6_89 a118

theorem c31264 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro a102 n185 n71 n120
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := h0
  have u5_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u6_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u7_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u5_101 u6_276
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u7_241 hv
  have u9_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u7_241 n185 u6_276 hv u0_316 u1_317 u2_318
  have u10_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u9_296 hv
  have u11_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u8_50 u10_86 u5_101
  have u12_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u8_50 u10_86 u5_101
  have u13_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u9_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u7_241 hv
  have u15_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u6_276 u5_101
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u4_121 a102 hv
  have u18_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28823 h hv u3_1 a102
  have u19_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u4_121 u5_101 a102 hv
  have u20_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c31258 h h0 hv n71 n120 a102
  have u21_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10719 h hv u8_50 u5_101 a102
  have u22_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2563 h hv u10_86 u5_101 a102
  have u23_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2703 h hv u10_86 u5_101 a102
  have u24_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1938 h u4_121 hv u17_119 n120
  have u25_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u4_121 u19_103 hv
  have u26_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6151 h hv u14_55 u24_110
  have u27_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2371 h hv u13_91 u24_110
  have u28_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c31263 h h0 hv u27_125 u25_118 u23_127 u22_126 u21_184 u20_240 u18_314 u10_86 u15_275 u16_315
  have u29_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1495 h hv u21_184 u20_240 u15_275 u28_311 u18_314 u16_315
  have u30_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u21_184 u20_240 u15_275 u29_305 u28_311 u18_314 u16_315
  have u31_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h u7_241 hv u30_100
  have u32_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h u9_296 u31_13 hv
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6976 h hv u32_64 u30_100 u17_119
  have u34_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7536 h hv u32_64 u30_100 u17_119
  have u35_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c192 h hv u27_125 u26_152 u33_157 u34_161 u12_167 u11_168
  exact c182 h u31_13 u27_125 u26_152 u33_157 u34_161 u35_164 u12_167 u11_168

private theorem c31265 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → Q {3, 4, 5, 6} → Q {1, 4, 5, 6} → ¬ Q {2, 3, 8, 9} → ¬ T {7, 8, 9} → False := by
  classical
  intro n116 n240 n305 n311 n125 n152 a296 a241 n275 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u2_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h a241 hv
  have u3_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h a296 hv
  have u4_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u2_50 u3_86 u1_101
  have u5_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u2_50 u3_86 u1_101
  have u6_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h a241 hv
  have u7_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv n116
  have u9_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10727 h hv u6_51 u1_101 u8_105
  have u10_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1499 h hv u9_184 n240 n275 n305 n311 u7_315
  have u11_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u9_184 n240 n275 n305 n311 u10_314 u7_315
  have u12_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h a241 hv u11_100
  have u13_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h a296 u12_13 hv
  have u14_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6974 h hv u13_64 u11_100 n116
  have u15_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7956 h hv u13_64 u11_100 n116
  have u16_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c190 h hv n125 n152 u14_157 u15_164 u5_167 u4_168
  exact c182 h u12_13 n125 n152 u14_157 u16_161 u15_164 u5_167 u4_168

private theorem c31266 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → T {6, 8, 9} → Q {3, 4, 5, 6} → Q {1, 4, 5, 6} → ¬ Q {2, 3, 8, 9} → ¬ T {7, 8, 9} → False := by
  classical
  intro n240 n305 n311 a119 a296 a241 n275 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h a296 hv
  have u2_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u1_86 a119
  have u3_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h a241 hv
  have u4_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6143 h hv u3_50 a119
  have u5_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u6_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u3_50 u1_86 u5_101
  have u7_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u3_50 u1_86 u5_101
  have u8_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h a241 hv
  have u9_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31265 h h0 hv n240 n305 n311 u2_125 u4_152 a296 a241 n275 n120
  have u11_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1935 h u0_121 hv u10_116 a119
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u11_110 hv
  have u13_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10743 h hv u8_55 u5_101 u12_111
  have u14_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1499 h hv u13_184 n240 n275 n305 n311 u9_315
  have u15_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u13_184 n240 n275 n305 n311 u14_314 u9_315
  have u16_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h a241 hv u15_100
  have u17_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h a296 u16_13 hv
  have u18_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7534 h hv u17_64 u15_100 u11_110
  have u19_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7954 h hv u17_64 u15_100 u11_110
  have u20_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u2_125 u4_152 u18_161 u19_164 u7_167 u6_168
  exact c182 h u16_13 u2_125 u4_152 u20_157 u18_161 u19_164 u7_167 u6_168

private theorem c31267 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n305 n311 n185 n71 n120
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u5_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u3_121 u4_102 hv
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u3_121 hv n120
  have u7_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u8_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u6_101 u7_276
  have u9_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u8_241 hv
  have u10_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u8_241 n185 u7_276 hv u0_316 u1_317 u2_318
  have u11_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u10_296 hv
  have u12_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8615 h hv u9_50 u11_86 u6_101
  have u13_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u10_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u8_241 hv
  have u15_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u7_276 u6_101
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u17_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c1788 h hv n120
  have u18_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31266 h h0 hv n305 n311 u5_119 u10_296 u8_241 u15_275 n120
  have u19_22 : T {0, 4, 5} := by
    by_contra hv
    exact c18556 h u18_240 hv n71 u4_102
  have u20_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c18471 h u18_240 u19_22 hv
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18469 h u18_240 hv u6_101
  have u22_73 : T {2, 4, 7} := by
    by_contra hv
    exact c18548 h u18_240 u21_13 hv u20_80
  have u23_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10637 h hv u14_55 u22_73
  have u24_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5595 h hv u22_73 u13_91
  have u25_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c1491 h u18_240 u23_184 u15_275 n305 n311 hv u16_315
  have u26_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28837 h u25_314 u19_22 hv
  have u27_36 : T {0, 8, 9} := by
    by_contra hv
    exact c26320 h u10_296 hv u26_41
  have u28_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c18621 h u8_241 u27_36 hv
  have u29_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12948 h hv u26_41 u28_68 u20_80
  have u30_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12108 h hv u26_41 u28_68 u20_80
  have u31_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c539 h hv u24_148 u12_169 u23_184 u30_194 u29_200 u17_204
  exact c527 h u27_36 u24_148 u12_169 u23_184 u30_194 u29_200 u31_203 u17_204

theorem c31268 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n311 n185 n71 n120
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u7_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u6_101 u5_276
  have u8_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u7_241 n185 u5_276 hv u0_316 u1_317 u2_318
  have u9_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u8_296 hv
  have u10_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u11_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u4_121 u10_102 hv
  have u12_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u9_86 u11_119
  have u13_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1299 h u8_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u7_241 hv
  have u15_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h u7_241 hv
  have u16_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u7_241 hv
  have u17_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u5_276 u6_101
  have u18_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u20_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv n120
  have u21_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c31267 h h0 hv n311 n185 n71 n120
  have u22_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u21_305 hv
  have u23_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h u21_305 hv
  have u24_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1494 h u21_305 hv
  have u25_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1644 h u21_305 hv
  have u26_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c27563 h u21_305 u3_1 hv
  have u27_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c27575 h u21_305 hv u14_55
  have u28_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7469 h hv u13_87 u22_89 u23_90
  have u29_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5509 h hv u9_86 u13_87 u22_89
  have u30_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2665 h hv u9_86 u13_87 u22_89
  have u31_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16289 h hv u9_86 u13_87 u22_89
  have u32_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5369 h hv u9_86 u13_87 u23_90
  have u33_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2525 h hv u9_86 u13_87 u23_90
  have u34_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16149 h hv u9_86 u13_87 u23_90
  have u35_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2247 h hv u9_86 u22_89 u23_90
  have u36_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2107 h hv u13_87 u22_89 u23_90
  have u37_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1935 h u4_121 u25_110 hv u11_119
  have u38_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1872 h u4_121 u10_102 u26_111 hv
  have u39_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1870 h u4_121 u10_102 u26_111 hv
  have u40_64 : T {1, 8, 9} := by
    by_contra hv
    exact c26310 h u8_296 u27_13 hv
  have u41_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c4 h u4_121 hv u36_123 u35_124 u12_125 u33_126 u30_127
  have u42_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u4_121 hv u37_116
  have u43_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1813 h u4_121 hv u38_115
  have u44_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u4_121 hv u39_114
  have u45_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7395 h hv u40_64 u24_100 u25_110
  have u46_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5995 h hv u40_64 u25_110 u11_119
  have u47_3 : T {0, 1, 4} := by
    by_contra hv
    exact c33 h u41_122 hv
  have u48_38 : T {1, 2, 4} := by
    by_contra hv
    exact c558 h u41_122 hv
  have u49_96 : ¬ T {3, 6, 8} := by
    intro hv
    exact c1953 h u41_122 hv u38_115
  have u50_97 : ¬ T {3, 6, 9} := by
    intro hv
    exact c1955 h u41_122 hv u39_114
  have u51_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10727 h hv u15_51 u6_101 u42_105
  have u52_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7635 h hv u15_51 u13_87 u42_105
  have u53_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7775 h hv u15_51 u13_87 u42_105
  have u54_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28891 h hv u47_3 u48_38 u16_50
  have u55_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c152 h hv u36_123 u46_150 u18_155 u45_160 u28_161 u52_162 u53_163
  have u56_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1495 h u21_305 u51_184 hv u17_275 n311 u54_314 u19_315
  have u57_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18488 h u56_240 u55_11 hv u27_13
  have u58_76 : T {2, 5, 6} := by
    by_contra hv
    exact c18530 h u56_240 u55_11 n71 hv
  have u59_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18324 h hv u55_11 u43_106
  have u60_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18184 h hv u55_11 u44_107
  have u61_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19724 h hv u55_11 u49_96
  have u62_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19584 h hv u55_11 u50_97
  have u63_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20567 h hv u57_12 u22_89
  have u64_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20427 h hv u57_12 u23_90
  have u65_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c27569 h u21_305 hv u58_76
  have u66_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c944 h hv u29_147 u31_224 u59_239 u61_249 u63_255 u20_260
  have u67_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c929 h hv u32_146 u34_223 u60_238 u62_248 u64_254 u20_260
  have u68_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c917 h hv u32_146 u34_223 u60_238 u62_248 u64_254 u67_257 u20_260
  have u69_63 : ¬ T {1, 7, 9} := by
    intro hv
    exact c932 h hv u29_147 u31_224 u59_239 u61_249 u63_255 u66_258 u20_260
  exact c26374 h u8_296 u65_6 u68_62 u69_63

end BorsukNine.FiniteObstruction

end OAI

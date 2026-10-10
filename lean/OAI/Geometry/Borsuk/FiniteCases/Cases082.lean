import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases024
import OAI.Geometry.Borsuk.FiniteCases.Cases031
import OAI.Geometry.Borsuk.FiniteCases.Cases073
import OAI.Geometry.Borsuk.FiniteCases.Cases081

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31253 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → T {4, 5, 7} → ¬ Q {0, 4, 5, 7} → False := by
  classical
  intro n242 n277 a102 n186
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1525 h hv n186 n242 n277 u2_316 u1_319 u0_320
  exact c1517 h a102 n186 n242 n277 u3_297 u2_316 u1_319 u0_320

theorem c31254 (h : TenSystem T Q) :
    T {0, 1, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → False := by
  classical
  intro a5 n139 n124 n130 n145 n143 n144
  have u0_135 : Q {0, 1, 4, 6} := by
    by_contra hv
    exact c62 h a5 n124 n130 hv n139 n143 n144 n145
  exact c68 h u0_135 n124 n130 n139 n143 n144 n145

private theorem c31255 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 3, 6} → ¬ T {2, 5, 7} → T {3, 4, 7} → ¬ Q {0, 1, 2, 6} → False := by
  classical
  intro a305 n145 n144 n143 n130 n77 a88 n124
  have u0_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h a305 hv
  have u1_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h a305 hv
  have u2_5 : T {0, 1, 6} := by
    by_contra hv
    exact c27566 h a305 hv n77
  have u3_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4389 h hv a88 u0_89 u1_90
  exact c31254 h u2_5 u3_139 n124 n130 n145 n143 n144

private theorem c31256 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ Q {3, 5, 8, 9} → Q {1, 3, 8, 9} → ¬ T {6, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n101 n311 a240 n119 n22
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_49 : T {1, 3, 9} := by
    by_contra hv
    exact c735 h a240 hv
  have u6_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h a240 hv
  have u7_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23707 h hv u0_2 u6_48 u5_49
  have u8_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u9_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv n119
  have u10_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv u7_277 u9_102 u8_186
  have u11_297 : Q {3, 4, 5, 7} := by
    by_contra hv
    exact c1521 h u10_242 u8_186 u7_277 hv u1_316 u2_319 u3_320
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1314 h u11_297 hv
  have u13_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1286 h u11_297 hv
  have u14_52 : T {1, 4, 7} := by
    by_contra hv
    exact c774 h u10_242 hv
  have u15_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u10_242 hv
  have u16_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u17_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2241 h hv u16_100 u9_102
  have u18_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18470 h a240 n22 hv
  have u19_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv n119
  have u20_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c31252 h h0 hv n22
  have u21_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u4_121 n101 hv
  have u22_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18468 h a240 hv n101
  have u23_71 : T {2, 4, 5} := by
    by_contra hv
    exact c18554 h a240 n22 hv n101
  have u24_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18549 h a240 u22_13 hv u18_80
  have u25_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18551 h a240 u22_13 hv u18_80
  have u26_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u23_71 u21_120
  have u27_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4891 h hv u23_71 u16_100
  have u28_27 : T {0, 5, 6} := by
    by_contra hv
    exact c18476 h a240 hv u24_73
  have u29_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10717 h hv u15_50 u23_71 u9_102
  have u30_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5115 h hv u23_71 u13_86 u9_102
  have u31_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5255 h hv u23_71 u13_86 u9_102
  have u32_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31255 h hv u31_145 u30_144 u27_143 u26_130 u25_77 u12_88 u17_124
  have u33_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23377 h hv u28_27 u14_52
  exact c1491 h a240 u29_184 u33_275 u32_305 n311 u19_314 u20_315

private theorem c31257 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → Q {1, 3, 8, 9} → ¬ T {6, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n311 a240 n119 n22
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_49 : T {1, 3, 9} := by
    by_contra hv
    exact c735 h a240 hv
  have u6_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h a240 hv
  have u7_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23707 h hv u0_2 u6_48 u5_49
  have u8_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u9_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv n119
  have u10_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv u7_277 u9_102 u8_186
  have u11_297 : Q {3, 4, 5, 7} := by
    by_contra hv
    exact c1521 h u10_242 u8_186 u7_277 hv u1_316 u2_319 u3_320
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1314 h u11_297 hv
  have u13_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1286 h u11_297 hv
  have u14_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u10_242 hv
  have u15_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u16_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2241 h hv u15_100 u9_102
  have u17_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18467 h a240 hv u9_102
  have u18_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv n119
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c31252 h h0 hv n22
  have u20_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31256 h h0 hv n311 a240 n119 n22
  have u21_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10719 h hv u14_50 u20_101 u9_102
  have u22_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23461 h hv u14_50 u20_101 u9_102
  have u23_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u4_121 u20_101 hv
  have u24_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u4_121 u20_101 u9_102 hv
  have u25_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1825 h u4_121 u20_101 u9_102 hv
  have u26_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18469 h a240 hv u20_101
  have u27_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c18561 h a240 hv u20_101 u9_102
  have u28_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1491 h a240 u21_184 u22_275 hv n311 u18_314 u19_315
  have u29_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13842 h hv n22 u23_120
  have u30_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15758 h hv n22 u24_103 u25_104
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18488 h a240 hv u17_12 u26_13
  have u32_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3062 h hv u27_71 u23_120
  have u33_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4978 h hv u27_71 u24_103 u25_104
  have u34_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u28_305 hv
  have u35_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h u28_305 hv
  have u36_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c27571 h u28_305 u31_11 hv
  have u37_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5229 h hv u13_86 u12_88 u34_89
  have u38_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4389 h hv u12_88 u34_89 u35_90
  have u39_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15169 h hv u12_88 u34_89 u35_90
  have u40_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16009 h hv u13_86 u12_88 u34_89
  have u41_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5089 h hv u13_86 u12_88 u35_90
  have u42_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15869 h hv u13_86 u12_88 u35_90
  have u43_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c31254 h hv u38_139 u16_124 u32_130 u37_145 u33_143 u41_144
  have u44_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c593 h hv u16_124 u29_207 u39_216 u30_220 u42_221 u40_222
  have u45_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c587 h hv u16_124 u29_207 u44_212 u39_216 u30_220 u42_221 u40_222
  exact c27640 h u28_305 u43_5 u45_40 u36_59

theorem c31258 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 8, 9} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a240 n71 n120 a102
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv n120
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1825 h u1_121 u2_101 a102 hv
  have u4_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u1_121 u2_101 a102 hv
  have u5_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17860 h hv n71 u4_103 u3_104
  have u6_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10020 h hv n71 u4_103 u3_104
  have u7_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u8_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u1_121 u4_103 hv
  have u9_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u1_121 a102 hv
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1940 h u1_121 hv u9_119 n120
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26863 h hv u0_1 u10_116
  have u12_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1938 h u1_121 hv u9_119 n120
  have u13_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27703 h hv u0_1 u12_110
  have u14_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u1_121 u12_110 hv
  have u15_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h a240 hv
  have u16_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u17_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c18559 h a240 hv u2_101 a102
  have u18_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31257 h h0 hv a240 u9_119 u17_22
  have u19_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18462 h a240 hv u14_111
  have u20_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22801 h hv u15_64 u12_110 u10_116
  have u21_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6975 h hv u15_64 u16_100 u10_116
  have u22_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6835 h hv u15_64 u16_100 u10_116
  have u23_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28662 h hv u17_22 n71 u3_104
  have u24_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28802 h hv u17_22 n71 u4_103
  have u25_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u18_311 hv
  have u26_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c28411 h u18_311 u19_10 hv
  have u27_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u6_179 u5_235 u20_270 u11_300 u13_306 u23_312 u24_313
  have u28_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u25_93 u8_118
  have u29_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7098 h hv u26_59 u27_95 u14_111
  have u30_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7238 h hv u26_59 u27_95 u14_111
  have u31_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c141 h hv u28_122 u7_155 u22_156 u21_157 u29_158 u30_159
  exact c137 h u19_10 u28_122 u31_149 u7_155 u22_156 u21_157 u29_158 u30_159

theorem c31261 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → T {4, 5, 6} → ¬ Q {2, 4, 5, 6} → False := by
  classical
  intro n185 n241 a101 n276
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1502 h a101 n185 n241 n276 hv u0_316 u1_317 u2_318
  exact c1510 h u3_296 n185 n241 n276 u0_316 u1_317 u2_318

theorem c31262 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 8, 9} → ¬ Q {2, 4, 5, 6} → T {4, 5, 6} → False := by
  classical
  intro a275 n276 a101
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_69 : T {2, 3, 8} := by
    by_contra hv
    exact c1035 h a275 hv
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1050 h a275 hv
  have u4_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10827 h hv u0_37 u2_69 u3_70
  have u5_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18667 h hv u1_9 u2_69 u3_70
  exact c31261 h h0 u4_185 u5_241 a101 n276

end BorsukNine.FiniteObstruction

end OAI

import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases098

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31508 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a63 n239 n258 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31506 h h0 hv n258 a313 a304
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u3_109 hv u4_118
  have u6_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u5_115
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u3_109 u4_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv u7_120
  have u9_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u7_120
  have u10_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c31507 h h0 hv a63 u2_71 a313 a304
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13842 h hv u10_22 u7_120
  have u12_42 : T {1, 2, 8} := by
    by_contra hv
    exact c28696 h a313 u10_22 hv
  have u13_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c27437 h a304 hv u12_42
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28745 h a313 u0_1 hv u12_42
  have u15_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c28747 h a313 u0_1 hv u12_42
  have u16_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13562 h hv u13_27 u7_120
  have u17_29 : T {0, 5, 8} := by
    by_contra hv
    exact c28700 h a313 hv u14_38
  have u18_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u15_39
  have u19_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28698 h a313 hv u15_39
  have u20_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u15_39
  have u21_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14315 h hv u19_25 u17_29 u20_32
  have u22_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16281 h hv u19_25 u17_29 u20_32
  have u23_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14027 h hv u19_25 u17_29 u20_32
  have u24_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c544 h u1_121 u16_205 u18_206 u11_207 u23_208 hv u21_210
  have u25_69 : T {2, 3, 8} := by
    by_contra hv
    exact c1025 h u24_209 hv
  have u26_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5449 h hv u25_69 u8_101
  have u27_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c940 h hv u26_147 u22_224 n239 u6_255 n258 u9_260
  exact c932 h a63 u26_147 u22_224 n239 u27_249 u6_255 n258 u9_260

private theorem c31509 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 5} → ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n22 n63 a71 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u6_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u5_118
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u7_109 u5_118 hv
  have u9_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u8_120
  have u10_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u7_109 hv u5_118
  have u11_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u1_1 hv
  have u12_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c324 h hv n22
  have u13_42 : T {1, 2, 8} := by
    by_contra hv
    exact c28696 h a313 n22 hv
  have u14_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28800 h a313 n22 hv u11_103
  have u15_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28745 h a313 u1_1 hv u13_42
  have u16_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27487 h a304 u1_1 hv u13_42
  have u17_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv u14_50 u5_118
  have u18_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10435 h hv u14_50 a71 u9_101
  have u19_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10715 h hv u14_50 a71 u9_101
  have u20_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c28695 h a313 hv u14_50
  have u21_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u15_38 u10_115
  have u22_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9084 h hv u16_40 u10_115
  have u23_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26312 h hv u20_14 n63
  have u24_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c295 h hv u6_132 u17_153 u22_173 u21_180 u18_182 u19_184
  have u25_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c287 h hv u6_132 u17_153 u22_173 u24_177 u21_180 u18_182 u19_184
  have u26_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23512 h hv u25_20 n63
  have u27_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u12_185 hv u9_101 u26_276
  exact c1506 h u27_241 u12_185 u26_276 u23_296 u4_316 u3_317 u2_318

private theorem c31510 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n38 n63 a71 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u1_121 u3_103 u2_112 hv
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv u4_116
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u6_109 u7_118 hv
  have u9_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u6_109 hv u7_118
  have u10_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6130 h hv n63 u9_115 u8_120
  have u11_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5848 h hv n63 u9_115 u8_120
  have u12_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u13_22 : T {0, 4, 5} := by
    by_contra hv
    exact c31509 h h0 hv n63 a71 a313 a304
  have u14_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 u13_22 hv
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u12_7 u14_42 hv
  have u16_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u12_7 u14_42 hv
  have u17_60 : T {1, 6, 8} := by
    by_contra hv
    exact c27508 h a304 u12_7 u14_42 hv
  have u18_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6187 h hv u16_53 u15_57 u17_60
  have u19_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5867 h hv u16_53 u7_118
  have u20_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6475 h hv u16_53 u15_57 u17_60
  have u21_153 : Q {0, 2, 3, 8} := by
    by_contra hv
    exact c124 h u1_121 u11_149 u19_150 u10_151 u18_152 hv u20_154
  have u22_58 : T {1, 5, 9} := by
    by_contra hv
    exact c6294 h u21_153 hv u5_105
  have u23_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u1_121 u3_103 u2_112 hv
  have u24_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u1_121 hv u23_114
  have u25_56 : T {1, 5, 7} := by
    by_contra hv
    exact c6292 h u21_153 hv u24_107
  have u26_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28691 h a313 hv u15_57
  have u27_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9788 h hv u14_42 u5_105
  have u28_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9506 h hv u14_42 u24_107
  have u29_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u12_7 hv
  have u30_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u7_118
  have u31_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv n38 u9_115
  have u32_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9362 h hv n38 u8_120
  have u33_29 : T {0, 5, 8} := by
    by_contra hv
    exact c28700 h a313 hv n38
  have u34_39 : T {1, 2, 5} := by
    by_contra hv
    exact c28748 h a313 n38 hv u14_42
  have u35_74 : T {2, 4, 8} := by
    by_contra hv
    exact c28776 h a313 u26_10 n38 hv
  have u36_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u33_29 hv
  have u37_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9115 h hv u34_39 u25_56 u22_58
  have u38_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10411 h hv u34_39 a71 u29_76
  have u39_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10691 h hv u34_39 a71 u29_76
  have u40_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c2927 h hv u35_74 u7_118
  have u41_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u36_40 u8_120
  have u42_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c291 h u21_153 u30_132 u37_173 hv u31_180 u38_182 u39_184
  exact c254 h u42_177 u40_129 u19_150 u41_170 u32_175 u28_176 u27_178

theorem c31511 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n63 a71 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u3_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u2_7 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u5_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u4_118
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u6_109 u4_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv u7_120
  have u9_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u6_109 hv u4_118
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u11_22 : T {0, 4, 5} := by
    by_contra hv
    exact c31509 h h0 hv n63 a71 a313 a304
  have u12_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14123 h hv u11_22 u4_118
  have u13_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18555 h hv u11_22 a71 u8_101
  have u14_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18275 h hv u11_22 a71 u8_101
  have u15_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 u11_22 hv
  have u16_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28799 h a313 u11_22 hv a71
  have u17_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u2_7 u15_42 hv
  have u18_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u2_7 u15_42 hv
  have u19_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c742 h hv u16_50
  have u20_14 : T {0, 2, 8} := by
    by_contra hv
    exact c28694 h a313 hv u16_50
  have u21_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28691 h a313 hv u18_57
  have u22_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u18_57
  have u23_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17207 h hv u20_14 u6_109
  have u24_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17902 h hv u21_10 u9_115
  have u25_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16924 h hv u22_12 u9_115
  have u26_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c715 h hv u5_132 u12_209 u25_229 u24_236 u14_238 u13_240
  have u27_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31510 h h0 hv n63 a71 a313 a304
  have u28_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c28701 h a313 hv u27_38
  have u29_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c28781 h a313 u27_38 a71 hv
  have u30_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c28743 h a313 u0_1 u27_38 hv
  have u31_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28753 h a313 hv u27_38 u17_53
  have u32_78 : T {2, 5, 8} := by
    by_contra hv
    exact c28818 h a313 u28_29 hv u10_103
  have u33_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27478 h a304 u2_7 u28_29 hv
  have u34_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28738 h a313 u2_7 hv u28_29
  have u35_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3066 h hv u29_74 u9_115
  have u36_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u30_39
  have u37_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u31_3
  have u38_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3513 h hv a71 u3_76 u32_78
  have u39_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3231 h hv a71 u3_76 u32_78
  have u40_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17387 h hv u20_14 u34_25 u33_32
  have u41_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17675 h hv u20_14 u34_25 u33_32
  have u42_129 : Q {0, 1, 3, 5} := by
    by_contra hv
    exact c19 h u1_121 u37_128 hv u35_130 u39_131 u5_132 u38_133
  exact c664 h u42_129 u36_206 u19_226 u23_231 u40_232 u26_233 u41_234

end BorsukNine.FiniteObstruction

end OAI

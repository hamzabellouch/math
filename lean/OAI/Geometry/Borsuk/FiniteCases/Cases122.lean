import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases121

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32659 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 8, 9} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n291 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32658 h h0 hv n105 n24
  have u2_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1395 h hv u1_93
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u3_116 hv u2_311 n291
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c435 h u5_200 hv
  have u7_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31604 h h0 u5_200 n291 hv u2_311
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c20830 h u7_256 n24 hv n105
  have u9_67 : T {2, 3, 6} := by
    by_contra hv
    exact c20718 h u7_256 n24 hv
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c12867 h u5_200 hv u8_88
  have u11_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19739 h hv u6_29 u9_67
  have u12_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c590 h hv u10_40
  have u13_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31322 h h0 u4_193 hv u11_249 u0_304
  have u14_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32652 h h0 hv u12_207 u6_29 n105 n24
  exact c31643 h h0 u13_109 u14_112

theorem c32660 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u1_49
  have u3_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u4_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32658 h h0 hv n105 n24
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1391 h hv u4_93
  have u6_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c32659 h h0 hv n105 n24
  have u7_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u6_291 n24 hv n105
  have u8_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c25607 h u6_291 hv u7_88
  have u9_46 : T {1, 3, 6} := by
    by_contra hv
    exact c25618 h u6_291 n24 hv
  have u10_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24626 h hv u8_5 u4_93
  have u11_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c32324 h h0 u9_46 hv u6_291
  have u12_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c32326 h h0 u9_46 hv u6_291
  have u13_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c31574 h h0 hv u10_284 u3_193 u0_304
  have u14_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31572 h h0 u13_249 u3_193 hv u0_304 u10_284
  have u15_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12336 h hv u11_44 u12_47 u1_49
  have u16_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u14_109 hv
  have u17_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c31587 h h0 hv u5_307 u15_196 u2_287
  exact c32634 h h0 u5_307 u17_252 u2_287 u16_112

private theorem c32661 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 4} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 8} → ¬ T {2, 5, 8} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 1, 7, 8} → T {3, 5, 9} → T {3, 8, 9} → ¬ Q {1, 2, 7, 9} → ¬ T {0, 2, 9} → Q {0, 5, 6, 8} → Q {1, 5, 6, 8} → ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro n44 n129 n132 n78 n140 n146 a94 a100 n224 n15 a196 a252 n109 n24
  have u0_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u1_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u2_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3072 h hv n78 n109
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h a252 n24 hv
  have u4_32 : T {0, 6, 8} := by
    by_contra hv
    exact c476 h a196 hv
  have u5_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18757 h hv u4_32 u3_70
  have u6_27 : T {0, 5, 6} := by
    by_contra hv
    exact c403 h a196 hv
  have u7_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19597 h hv u6_27 u3_70
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u8_105 hv
  have u10_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 a252 hv u3_70
  have u11_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4882 h hv u10_65 u9_116
  have u12_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12317 h a196 hv u3_70
  have u13_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h a252 n24 hv n109
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u15_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c1625 h hv n109
  have u16_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c348 h hv n24
  have u17_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c648 h hv n44
  have u18_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12338 h a196 hv n44 u12_52
  have u19_84 : T {2, 7, 9} := by
    by_contra hv
    exact c12310 h a196 n44 hv
  have u20_90 : T {3, 4, 9} := by
    by_contra hv
    exact c12396 h a196 n44 u10_65 hv
  have u21_131 : Q {0, 1, 3, 7} := by
    by_contra hv
    exact c31533 h h0 n129 n132 u17_128 u0_133 hv u2_130
  have u22_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c12375 h a196 u18_38 u13_73 hv
  have u23_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c20151 h a252 hv u19_84
  have u24_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2369 h hv u20_90 u14_112
  have u25_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20957 h hv u3_70 u20_90 a94
  have u26_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20117 h hv u3_70 u20_90 a100
  have u27_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16097 h hv u6_27 u20_90
  have u28_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15257 h hv u4_32 u20_90
  have u29_147 : Q {0, 1, 7, 9} := by
    by_contra hv
    exact c81 h u21_131 u24_125 u16_136 n140 u11_143 n146 hv
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c3304 h u21_131 n78 hv u9_116
  have u31_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c3219 h u21_131 hv u30_103
  have u32_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20510 h hv n15 u22_75 u31_82
  have u33_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18268 h hv n15 u22_75 u31_82
  have u34_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17426 h hv n15 u22_75 u31_82
  have u35_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c20990 h hv u23_16 n78
  have u36_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c931 h hv n146 u27_223 u33_238 u7_248 u32_254 u25_257
  have u37_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c841 h hv n140 u28_217 u34_232 u5_242 u26_251 u32_254
  exact c934 h u29_147 n224 u1_239 u15_249 u37_255 u35_258 u36_260

theorem c32662 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 5, 8} → T {3, 4, 7} → ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro n93 a88 n109 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u3_105 hv
  have u5_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13844 h hv n24 u4_116
  have u6_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u7_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u8_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1391 h hv n93
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32590 h h0 n93 u7_189 u3_105 hv
  have u10_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 u8_307 hv u6_287 u2_112
  have u11_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u10_252 hv
  have u12_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u10_252 u8_307 hv u6_287
  have u13_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h u10_252 n24 hv
  have u14_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 u10_252 hv u13_70
  have u15_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32086 h h0 u10_252 u13_70 hv
  have u16_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h u10_252 n24 hv n109
  have u17_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c20155 h u10_252 hv u16_73
  have u18_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c20149 h u10_252 hv a88
  have u19_26 : T {0, 4, 9} := by
    by_contra hv
    exact c20158 h u10_252 hv u15_68
  have u20_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10219 h hv u11_57 u16_73
  have u21_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c12309 h u12_196 hv a88
  have u22_54 : T {1, 4, 9} := by
    by_contra hv
    exact c12354 h u12_196 u21_43 u0_49 hv
  have u23_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12317 h u12_196 hv u13_70
  have u24_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv u9_29 u13_70
  have u25_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c969 h hv u14_65
  have u26_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c1016 h hv u15_68
  have u27_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c643 h hv u21_43
  have u28_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6004 h hv u23_52 u4_116
  have u29_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22904 h hv n24 u23_52 n109
  have u30_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22196 h hv n24 u23_52 n109
  have u31_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 hv u24_245 u3_105 u7_189
  have u32_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1006 h hv u28_151 u5_207 u25_262 u30_266 u26_270 u29_271
  have u33_72 : T {2, 4, 6} := by
    by_contra hv
    exact c1076 h u31_280 hv
  have u34_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u31_280 u24_245 u7_189 hv
  have u35_100 : T {3, 8, 9} := by
    by_contra hv
    exact c24172 h u31_280 u17_21 u0_49 hv
  have u36_8 : T {0, 1, 9} := by
    by_contra hv
    exact c24068 h u31_280 hv n93
  have u37_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32210 h h0 u31_280 hv u36_8
  have u38_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c32209 h h0 u31_280 hv u36_8
  have u39_94 : T {3, 5, 9} := by
    by_contra hv
    exact c24170 h u31_280 u17_21 u0_49 hv
  have u40_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5313 h hv u33_72 u39_94
  have u41_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4471 h hv u33_72 u35_100
  have u42_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c26979 h u34_300 u9_29 u11_57 hv
  have u43_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c95 h hv u37_7
  have u44_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c50 h hv u38_4
  have u45_44 : T {1, 3, 4} := by
    by_contra hv
    exact c32661 h h0 hv u44_129 u43_132 u42_78 u41_140 u40_146 u39_94 u35_100 u27_224 u18_15 u12_196 u10_252 n109 n24
  have u46_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c12311 h u12_196 u45_44 hv
  have u47_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c31881 h h0 u45_44 hv u12_196
  have u48_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c12399 h u12_196 u45_44 a88 hv
  have u49_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c12341 h u12_196 hv u45_44 u22_54
  have u50_41 : T {1, 2, 7} := by
    by_contra hv
    exact c12380 h u12_196 hv u15_68 u46_84
  have u51_75 : T {2, 4, 9} := by
    by_contra hv
    exact c12390 h u12_196 u21_43 hv u46_84
  have u52_13 : T {0, 2, 7} := by
    by_contra hv
    exact c20220 h u10_252 hv u15_68 u46_84
  have u53_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c701 h hv u47_47
  have u54_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1346 h hv u48_90
  have u55_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9922 h hv u49_38 u4_116
  have u56_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28083 h hv u52_13 u50_41 u16_73
  have u57_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28931 h hv u52_13 u50_41 u16_73
  have u58_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27827 h hv u19_26 u22_54 u51_75
  have u59_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28667 h hv u19_26 u22_54 u51_75
  have u60_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1454 h hv u20_181 u1_237 u32_272 u54_302 u56_308 u57_314
  exact c1420 h u34_300 u55_179 u53_235 u26_270 u58_306 u59_312 u60_313

end BorsukNine.FiniteObstruction

end OAI

import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases122

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32663 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 6, 8} → T {3, 5, 8} → T {5, 6, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro n307 a93 a112 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u2_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u3_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u4_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 n307 hv u2_287 a112
  have u5_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u4_252 hv
  have u6_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u4_252 n307 hv u2_287
  have u7_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h u4_252 n24 hv
  have u8_29 : T {0, 5, 8} := by
    by_contra hv
    exact c431 h u6_196 hv
  have u9_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv u8_29 u7_70
  have u10_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24179 h hv u8_29 u5_57 a93
  exact c31281 h h0 u10_280 u9_245 u1_105 u3_189

private theorem c32664 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → T {2, 3, 9} → T {1, 5, 8} → T {3, 5, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro a29 a70 a57 a93 n24
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u1_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u2_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24179 h hv a29 a57 a93
  have u3_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 a70
  exact c31281 h h0 u2_280 u3_245 u0_105 u1_189

theorem c32665 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 3, 5, 9} → T {2, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 8, 9} → False := by
  classical
  intro n269 a70 n154 n274 n265 n275
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_272 : Q {2, 3, 6, 9} := by
    by_contra hv
    exact c1037 h a70 n154 u0_210 n265 n269 hv n274 n275
  exact c1047 h u1_272 n154 u0_210 n265 n269 n274 n275

private theorem c32666 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 4, 7} → ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro a88 n109 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u3_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u4_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u5_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32662 h h0 hv a88 n109 n24
  have u6_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32663 h h0 hv u5_93 u1_112 n24
  have u7_43 : T {1, 2, 9} := by
    by_contra hv
    exact c27856 h u6_307 n24 hv
  have u8_52 : T {1, 4, 7} := by
    by_contra hv
    exact c27960 h u6_307 n24 hv n109
  have u9_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12309 h hv u7_43 a88
  have u10_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6427 h hv u8_52 u1_112
  have u11_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c31589 h h0 u6_307 hv u9_196 u3_287
  have u12_55 : T {1, 5, 6} := by
    by_contra hv
    exact c823 h u11_252 hv
  have u13_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u11_252 hv
  have u14_60 : T {1, 6, 8} := by
    by_contra hv
    exact c896 h u11_252 hv
  have u15_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h u11_252 n24 hv
  have u16_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 u11_252 hv u15_70
  have u17_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32086 h h0 u11_252 u15_70 hv
  have u18_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c975 h hv u16_65
  have u19_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c1020 h hv u17_68
  have u20_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32664 h h0 hv u15_70 u13_57 u5_93 n24
  have u21_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv u20_29 u0_49
  have u22_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u21_280 hv u2_105 u4_189
  have u23_51 : T {1, 4, 6} := by
    by_contra hv
    exact c761 h u22_245 hv
  have u24_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u22_245 hv
  have u25_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23445 h hv u23_51 u12_55 u24_59
  have u26_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22597 h hv u23_51 u24_59 u14_60
  exact c32665 h h0 u26_269 u15_70 u10_154 u19_274 u18_265 u25_275

private theorem c32667 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 3, 4} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 3, 6} → T {1, 8, 9} → T {1, 5, 9} → ¬ Q {0, 2, 3, 9} → T {0, 4, 9} → T {3, 4, 9} → ¬ Q {1, 2, 6, 7} → Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → T {0, 5, 8} → Q {1, 4, 6, 7} → ¬ T {5, 8, 9} → False := by
  classical
  intro n65 n150 n153 n151 a64 a58 n154 a26 a90 n220 a196 n38 a29 a245 n116
  have u0_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c963 h hv n65
  have u1_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4882 h hv n65 n116
  have u2_75 : T {2, 4, 9} := by
    by_contra hv
    exact c12372 h a196 n38 n65 hv
  have u3_152 : Q {0, 2, 3, 7} := by
    by_contra hv
    exact c31534 h h0 n153 n150 u0_149 n154 hv n151
  have u4_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17777 h hv a29 u2_75
  have u5_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20127 h hv a26 u2_75 a90
  have u6_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20967 h hv a26 u2_75 a90
  have u7_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c6201 h u3_152 a58 hv a64
  have u8_258 : Q {1, 6, 7, 9} := by
    by_contra hv
    exact c880 h a245 u1_143 n220 u4_235 u5_251 u6_257 hv
  exact c913 h u8_258 u7_61

theorem c32668 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro n109 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u1_105 hv
  have u3_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u4_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u5_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u6_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c32666 h h0 hv n109 n24
  have u7_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1316 h hv u6_88
  have u8_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20262 h hv n24 u6_88 n109
  have u9_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u7_300 u4_189 u1_105
  have u10_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 hv u8_252 u3_287 u5_112
  have u11_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u9_280 hv
  have u12_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u9_280 hv u4_189 u7_300
  have u13_29 : T {0, 5, 8} := by
    by_contra hv
    exact c24076 h u9_280 hv u0_49
  have u14_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1391 h u10_307 hv
  have u15_43 : T {1, 2, 9} := by
    by_contra hv
    exact c27856 h u10_307 n24 hv
  have u16_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32485 h h0 u10_307 hv u15_43
  have u17_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32486 h h0 u10_307 u15_43 hv
  have u18_52 : T {1, 4, 7} := by
    by_contra hv
    exact c27960 h u10_307 n24 hv n109
  have u19_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31589 h h0 u10_307 u8_252 hv u3_287
  have u20_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c27849 h u10_307 hv u11_73
  have u21_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c19169 h u12_245 hv u14_93
  have u22_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24179 h u9_280 u13_29 hv u14_93
  have u23_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19177 h u12_245 u13_29 hv
  have u24_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv u16_38
  have u25_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c611 h hv u17_41
  have u26_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8804 h hv u17_41 u2_116
  have u27_90 : T {3, 4, 9} := by
    by_contra hv
    exact c12306 h u19_196 u17_41 hv
  have u28_26 : T {0, 4, 9} := by
    by_contra hv
    exact c27858 h u10_307 hv u17_41
  have u29_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6427 h hv u18_52 u5_112
  have u30_58 : T {1, 5, 9} := by
    by_contra hv
    exact c24146 h u9_280 u20_8 u0_49 hv
  have u31_64 : T {1, 8, 9} := by
    by_contra hv
    exact c24148 h u9_280 u20_8 u0_49 hv
  have u32_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6012 h hv u22_57 n109
  have u33_79 : T {2, 5, 9} := by
    by_contra hv
    exact c19246 h u12_245 u21_15 u23_70 hv
  have u34_85 : T {2, 8, 9} := by
    by_contra hv
    exact c19248 h u12_245 u21_15 u23_70 hv
  have u35_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c24073 h u9_280 hv u30_58
  have u36_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6295 h hv u30_58 u1_105
  have u37_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5881 h hv u31_64 u1_105
  have u38_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c24071 h u9_280 hv u31_64
  have u39_65 : T {2, 3, 4} := by
    by_contra hv
    exact c32667 h h0 hv u37_150 u36_153 u32_151 u31_64 u30_58 u29_154 u28_26 u27_90 u25_220 u19_196 u16_38 u13_29 u12_245 u2_116
  have u40_63 : ¬ T {1, 7, 9} := by
    intro hv
    exact c12321 h u19_196 hv u39_65
  have u41_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c31884 h h0 u39_65 u19_196 hv
  have u42_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c12397 h u19_196 hv u39_65 u27_90
  have u43_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c12377 h u19_196 u39_65 u11_73 hv
  have u44_84 : T {2, 7, 9} := by
    by_contra hv
    exact c12436 h u19_196 u40_63 hv n109
  have u45_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24210 h hv u38_17 u40_63
  have u46_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23512 h hv u35_20 u40_63
  have u47_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3764 h hv u41_68 u2_116
  have u48_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11618 h hv u22_57 u41_68
  have u49_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c654 h hv u42_44
  have u50_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c1121 h hv u43_75
  have u51_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c27947 h u10_307 hv u11_73 u44_84
  have u52_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27117 h hv u15_43 u33_79 u44_84
  have u53_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11551 h hv u15_43 u33_79 u44_84
  have u54_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26417 h hv u15_43 u44_84 u34_85
  have u55_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10851 h hv u15_43 u44_84 u34_85
  have u56_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c336 h hv u47_135 u26_171 u55_185 u4_189 u53_190 u48_191
  have u57_262 : Q {2, 3, 4, 6} := by
    by_contra hv
    exact c1077 h u9_280 u56_156 u24_212 hv u46_276 u45_281 u50_282
  have u58_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27152 h hv u51_13 u22_57
  exact c1298 h u57_262 u26_171 u49_227 u54_296 u7_300 u52_301 u58_302

theorem c32669 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → ¬ Q {0, 2, 3, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro a29 n154 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c32668 h h0 hv n24
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u4_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u5_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u4_193 u2_109 hv u0_304
  have u6_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u5_249 hv u4_193 u0_304
  have u7_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h u6_284 hv
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4707 h hv u7_73 u3_105 u2_109
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h u6_284 hv
  have u10_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u5_249 hv
  have u11_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6363 h hv u10_52 u3_105 u2_109
  have u12_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5933 h hv u10_52 u3_105 u2_109
  have u13_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv u10_52 u3_105 u2_109
  have u14_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u3_105 hv
  have u15_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u2_109 hv
  have u16_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31705 h h0 u14_116 hv u15_112
  have u17_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31632 h h0 u16_103 hv
  have u18_54 : T {1, 4, 9} := by
    by_contra hv
    exact c808 h u5_249 hv
  have u19_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u14_116 hv u15_112
  have u20_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6009 h hv u18_54 u19_114
  have u21_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u2_109
  have u22_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u3_105
  have u23_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u24_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c24639 h u6_284 a29 hv
  have u25_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u23_177 u8_141 a29 u22_200 u13_162 hv u21_196
  have u26_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c434 h u25_198 u8_141 u13_162 u23_177 hv u21_196 u22_200
  have u27_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12594 h u25_198 u1_49 hv
  have u28_44 : T {1, 3, 4} := by
    by_contra hv
    exact c12616 h u25_198 hv u24_46 u1_49
  have u29_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c12591 h u25_198 u28_44 hv
  have u30_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c12657 h u25_198 hv u27_72 u9_75
  have u31_61 : T {1, 6, 9} := by
    by_contra hv
    exact c11168 h u26_187 hv u29_82 u17_118
  have u32_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c963 h hv u30_65
  have u33_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6159 h hv u31_61 u16_103
  exact c31534 h h0 u11_153 u12_150 u32_149 n154 u33_152 u20_151

end BorsukNine.FiniteObstruction

end OAI

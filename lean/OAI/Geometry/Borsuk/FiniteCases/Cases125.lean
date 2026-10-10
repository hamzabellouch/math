import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases124

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32680 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {2, 4, 7, 9} → False := by
  classical
  intro n193 a109 n284
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 n193 a109 hv u0_304
  exact c31574 h h0 u1_249 n284 n193 u0_304

private theorem c32681 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → T {5, 8, 9} → Q {0, 4, 7, 9} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n46 n67 a116 a193 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u3_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u2_105
  have u4_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21785 h hv a29 u3_57 a116
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv a116
  have u6_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u7_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u8_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u9_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15857 h hv u7_21 u6_26 u8_35
  have u10_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15155 h hv u7_21 u6_26 u8_35
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u12_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19357 h hv u11_15 u7_21 u8_35
  have u13_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18655 h hv u11_15 u7_21 u8_35
  have u14_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20055 h hv u11_15 u7_21 u6_26
  have u15_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20895 h hv u11_15 u7_21 u6_26
  have u16_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u17_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 a193 u16_284 hv u1_304
  have u18_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u19_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u18_70
  have u20_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c684 h hv n46
  have u21_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c688 h hv n46
  have u22_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11892 h a193 n46 hv
  have u23_91 : T {3, 5, 6} := by
    by_contra hv
    exact c11982 h a193 n46 n67 hv
  have u24_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c12007 h a193 u3_57 u22_78 hv
  have u25_96 : T {3, 6, 8} := by
    by_contra hv
    exact c11984 h a193 n46 n67 hv
  have u26_12 : T {0, 2, 6} := by
    by_contra hv
    exact c19726 h u17_249 hv u24_93
  have u27_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c19725 h u17_249 hv u25_96
  have u28_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c19729 h u17_249 hv u23_91
  have u29_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9045 h hv u3_57 u22_78 a116
  have u30_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16885 h hv a29 u22_78 a116
  have u31_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32382 h h0 hv u26_12 u11_15
  have u32_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32443 h h0 hv u26_12 u11_15
  have u33_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u29_172 u30_228 u4_263 u31_297 u5_300 u32_303 u1_304
  have u34_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21126 h hv u27_11 u33_88
  have u35_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20288 h hv u28_14 u33_88
  have u36_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c889 h hv u9_221 u21_236 u12_246 u19_252 u15_257 u34_259
  have u37_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c814 h hv u10_216 u20_231 u13_241 u14_251 u19_252 u35_253
  have u38_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c887 h hv u36_144 u9_221 u21_236 u12_246 u19_252 u15_257 u34_259
  have u39_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c812 h hv u37_139 u10_216 u20_231 u13_241 u14_251 u19_252 u35_253
  exact c11932 h a193 n46 u39_55 u38_60

private theorem c32682 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {5, 6, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a116 n112 n280 a29 a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u5_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u4_109 u3_284
  have u6_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h u5_193 hv
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u8_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h u5_193 hv
  have u9_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17957 h hv u7_15 u8_26 u6_35
  have u10_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17255 h hv u7_15 u8_26 u6_35
  have u11_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u12_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15857 h hv u11_21 u8_26 u6_35
  have u13_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15155 h hv u11_21 u8_26 u6_35
  have u14_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19357 h hv u7_15 u11_21 u6_35
  have u15_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18655 h hv u7_15 u11_21 u6_35
  have u16_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20055 h hv u7_15 u11_21 u8_26
  have u17_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20895 h hv u7_15 u11_21 u8_26
  have u18_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 u5_193 u3_284 hv u2_304
  have u19_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv n112
  have u20_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c22959 h hv a29 u19_52
  have u21_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22197 h hv u1_24 u19_52 u4_109
  have u22_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u1_24 u19_52 u4_109
  have u23_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13853 h hv a29 u4_109
  have u24_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 n112
  have u25_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u26_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u1_24 u25_70
  have u27_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u28_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6005 h hv u19_52 a116
  have u29_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u27_105
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21645 h hv a29 u29_57 a116
  have u31_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21785 h hv a29 u29_57 a116
  have u32_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22781 h hv a29 u29_57 a116
  have u33_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c992 h hv u28_151 u23_207 u30_262 u21_266 u32_270 u22_271 u20_272
  have u34_46 : T {1, 3, 6} := by
    by_contra hv
    exact c32681 h h0 hv u33_67 a116 u5_193 a29 a154
  have u35_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c31853 h h0 u5_193 hv u34_46
  have u36_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c31851 h h0 u5_193 hv u34_46
  have u37_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c11893 h u5_193 u34_46 hv
  have u38_76 : T {2, 5, 6} := by
    by_contra hv
    exact c11894 h u5_193 u35_48 hv
  have u39_81 : T {2, 6, 8} := by
    by_contra hv
    exact c11890 h u5_193 u36_45 hv
  have u40_18 : T {0, 3, 6} := by
    by_contra hv
    exact c19732 h u18_249 hv u37_78
  have u41_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c19735 h u18_249 hv u38_76
  have u42_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c11963 h u5_193 hv u38_76 u39_81
  have u43_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c19731 h u18_249 hv u39_81
  have u44_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14685 h hv u40_18 a116
  have u45_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c32182 h h0 hv u40_18 u11_21
  have u46_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c32243 h h0 hv u40_18 u11_21
  have u47_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c1082 h hv u24_157 u44_213 u31_263 u45_277 n280 u46_283 u3_284
  have u48_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20294 h hv u41_20 u47_73
  have u49_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21132 h hv u43_17 u47_73
  have u50_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c814 h hv u13_216 u10_231 u15_241 u16_251 u26_252 u48_253
  have u51_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c889 h hv u12_221 u9_236 u14_246 u26_252 u17_257 u49_259
  have u52_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c812 h hv u50_139 u13_216 u10_231 u15_241 u16_251 u26_252 u48_253
  have u53_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c887 h hv u51_144 u12_221 u9_236 u14_246 u26_252 u17_257 u49_259
  exact c11930 h u5_193 u42_40 u52_55 u53_60

private theorem c32683 (h : TenSystem T Q) :
    ¬ Q {1, 5, 8, 9} → ¬ Q {1, 5, 7, 8} → T {1, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 2, 5, 8} → False := by
  classical
  intro n256 n254 a57 n243 n252 n233 n218
  have u0_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c842 h a57 hv n218 n233 n243 n252 n254 n256
  exact c844 h u0_141 n218 n233 n243 n252 n254 n256

theorem c32684 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n112 n280 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u3_70
  have u5_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u6_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u8_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u7_109 u2_284
  have u9_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h u8_193 hv
  have u10_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h u8_193 hv
  have u11_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 u8_193 u2_284 hv u1_304
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20475 h hv u6_15 u5_21 u9_26
  have u13_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18937 h hv u6_15 u5_21 u10_35
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17537 h hv u6_15 u9_26 u10_35
  have u15_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15437 h hv u5_21 u9_26 u10_35
  have u16_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32682 h h0 hv n112 n280 a29 a154
  have u17_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u11_249 a29 hv
  have u18_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv u16_116
  have u19_57 : T {1, 5, 8} := by
    by_contra hv
    exact c11898 h u8_193 hv u17_67
  exact c32683 h u18_256 u12_254 u19_57 u13_243 u4_252 u14_233 u15_218

private theorem c32686 (h : TenSystem T Q) :
    ¬ T {2, 3, 6} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → T {0, 5, 8} → False := by
  classical
  intro n67 n187 n198 n177 n162 n52 n109 a29
  have u0_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4604 h hv n67 n109
  have u1_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12878 h hv n52 n67
  have u2_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32648 h u0_141 n187 hv n198 a29 n177 n162
  exact c432 h u2_196 u0_141 n162 n177 n187 n198 u1_200

theorem c32687 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 8} → T {5, 6, 8} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a57 a112 a29 a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c6427 h a154 hv a112
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3909 h hv u3_70 a112
  have u5_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31847 h h0 hv a112
  have u6_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c6435 h a154 a57 hv
  have u8_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11337 h hv a57 u3_70
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c6535 h a154 a57 a112 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c6531 h a154 a57 hv a112
  have u11_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u7_105 hv
  have u12_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 u7_105
  have u13_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9746 h hv u2_52 u7_105 u6_109
  have u14_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u9_114
  have u15_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1533 h hv u10_103
  have u16_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6947 h hv a57 a112 u11_116
  have u17_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9047 h hv a57 a112 u11_116
  have u18_67 : T {2, 3, 6} := by
    by_contra hv
    exact c32686 h hv u15_187 u14_198 u13_177 u12_162 u2_52 u6_109 a29
  have u19_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31785 h h0 hv u18_67 u3_70
  have u20_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31846 h h0 hv u18_67 u3_70
  exact c347 h u1_24 u4_136 u16_157 u17_172 u19_186 u8_189 u20_192 u5_193

end BorsukNine.FiniteObstruction

end OAI

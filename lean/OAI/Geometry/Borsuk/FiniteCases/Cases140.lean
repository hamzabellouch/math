import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases139

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32781 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 5, 9} → T {1, 2, 9} → ¬ T {1, 4, 6} → False := by
  classical
  intro n58 a43 n51
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32778 h h0 hv n51
  have u6_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 hv u4_245 u5_300
  have u7_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u6_280 u4_245 hv u5_300
  have u8_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u7_189 hv
  have u9_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28137 h hv u8_23 a43
  have u10_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c11329 h u7_189 a43 hv
  have u11_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24184 h u6_280 hv u10_93 u1_116
  have u12_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c24075 h u6_280 hv u11_57
  have u13_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25334 h hv u12_21 n51
  have u14_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c11337 h u7_189 u11_57 hv
  have u15_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12596 h hv n51 u14_70
  have u16_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c31597 h h0 hv u9_309 u13_289 u15_198
  have u17_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31595 h h0 u16_254 u13_289 u9_309 u15_198 hv
  have u18_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31709 h h0 u1_116 u17_114 hv
  have u19_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c32047 h h0 hv u18_112
  have u20_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u7_189 u2_49 hv
  have u21_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31707 h h0 u1_116 u17_114 hv
  have u22_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5571 h hv u20_78 u21_103 u18_112
  have u23_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16351 h hv u0_29 u21_103 u18_112
  have u24_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c32137 h h0 hv u21_103
  have u25_8 : T {0, 1, 9} := by
    by_contra hv
    exact c24068 h u6_280 hv u10_93
  have u26_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32210 h h0 u6_280 hv u25_8
  have u27_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c105 h hv u26_7
  have u28_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c31810 h h0 u7_189 hv a43
  have u29_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c630 h hv u28_42
  have u30_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c32780 h h0 hv n51
  have u31_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c868 h hv n58
  have u32_64 : T {1, 8, 9} := by
    by_contra hv
    exact c24152 h u6_280 u2_49 n58 hv
  have u33_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c946 h hv u22_147 u23_224 u3_239 u19_249 u31_255 u24_258
  exact c32772 h h0 u33_260 u32_64 u30_259 u29_225 u27_148

private theorem c32782 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → ¬ T {1, 4, 6} → False := by
  classical
  intro a43 n51
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u4_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u5_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u6_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u7_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32778 h h0 hv n51
  have u8_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 hv u6_245 u7_300
  have u9_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u8_280 u6_245 hv u7_300
  have u10_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u9_189 u3_49 hv
  have u11_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u9_189 hv
  have u12_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c11329 h u9_189 a43 hv
  have u13_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c31810 h h0 u9_189 hv a43
  have u14_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28137 h hv u11_23 a43
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24184 h u8_280 hv u12_93 u0_116
  have u16_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c618 h hv u13_42
  have u17_94 : T {3, 5, 9} := by
    by_contra hv
    exact c11326 h u9_189 u13_42 hv
  have u18_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c24075 h u8_280 hv u15_57
  have u19_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c11337 h u9_189 u15_57 hv
  have u20_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25334 h hv u18_21 n51
  have u21_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12596 h hv n51 u19_70
  have u22_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c31597 h h0 hv u14_309 u20_289 u21_198
  have u23_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31595 h h0 u22_254 u20_289 u14_309 u21_198 hv
  have u24_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u23_114
  have u25_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31707 h h0 u0_116 u23_114 hv
  have u26_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31709 h h0 u0_116 u23_114 hv
  have u27_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31662 h h0 u24_107 hv u5_105
  have u28_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31658 h h0 hv u24_107 u5_105
  have u29_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13993 h hv u2_29 u24_107
  have u30_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18285 h hv u11_23 u1_72 u24_107
  have u31_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17437 h hv u11_23 u1_72 u24_107
  have u32_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17879 h hv u2_29 u10_78 u25_103
  have u33_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16883 h hv u2_29 u10_78 u26_112
  have u34_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31637 h h0 u27_106 hv
  have u35_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8248 h hv u3_49 u28_101
  have u36_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c31315 h u30_238 hv u4_239 u33_228 u31_232 u32_235 u29_208
  have u37_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8528 h hv u36_47 u28_101
  have u38_58 : T {1, 5, 9} := by
    by_contra hv
    exact c32781 h h0 hv a43 n51
  have u39_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c24073 h u8_280 hv u38_58
  have u40_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6295 h hv u38_58 u5_105
  have u41_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c11339 h u9_189 u38_58 hv
  have u42_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7093 h hv u38_58 u17_94 u34_115
  have u43_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8089 h hv u38_58 u17_94 u34_115
  have u44_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25474 h hv u39_20 n51
  have u45_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c205 h hv u16_126 u40_153 u42_158 u43_165 u35_167 u37_169
  have u46_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u42_158 u37_169 hv u35_167 u40_153 u43_165 u45_162
  have u47_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12736 h hv n51 u41_69
  have u48_310 : Q {3, 5, 7, 9} := by
    by_contra hv
    exact c31335 h h0 u34_115 hv u44_290 u47_199
  exact c28274 h u48_310 u46_14 n51

theorem c32783 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → T {3, 5, 8} → ¬ Q {3, 5, 7, 8} → False := by
  classical
  intro n298 n268 n177 n233 a93 n309
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32744 h h0 hv
  have u1_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c1382 h a93 n177 n233 n268 n298 hv n309 u0_311
  exact c1392 h u1_307 n177 n233 n268 n298 n309 u0_311

theorem c32784 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 6} → False := by
  classical
  intro n51
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u4_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u5_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u6_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv n51
  have u7_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32778 h h0 hv n51
  have u8_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 hv u5_245 u7_300
  have u9_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u8_280 hv
  have u10_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u8_280 u5_245 hv u7_300
  have u11_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17583 h hv u1_24 u9_73 u0_105
  have u12_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u10_189 u2_49 hv
  have u13_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c32780 h h0 hv n51
  have u14_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32782 h h0 hv n51
  have u15_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c641 h hv u14_43
  have u16_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11328 h u10_189 u14_43 hv
  have u17_64 : T {1, 8, 9} := by
    by_contra hv
    exact c11376 h u10_189 u14_43 u2_49 hv
  have u18_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c24069 h u8_280 hv u16_93
  have u19_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21115 h hv u3_29 u12_78 u16_93
  have u20_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u9_73 u16_93
  have u21_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c24071 h u8_280 hv u17_64
  have u22_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c11341 h u10_189 u17_64 hv
  have u23_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c912 h hv u20_145 u15_222 u4_237 u6_247 u19_258 u13_259
  have u24_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c253 h hv u21_17
  have u25_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c988 h hv u22_66
  have u26_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c902 h hv u20_145 u15_222 u4_237 u6_247 u23_253 u19_258 u13_259
  have u27_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28208 h hv u18_8 u14_43 u26_61
  have u28_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26666 h hv u18_8 u14_43 u26_61
  exact c32783 h h0 u28_298 u25_268 u24_177 u11_233 u16_93 u27_309

theorem c32785 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → False := by
  classical
  intro a274
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  exact c23239 h a274 u1_29 u0_51

theorem c32786 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → False := by
  classical
  intro a177
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c9735 h a177 u0_51 u1_72 u2_105

theorem c32787 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 8, 9} → False := by
  classical
  intro a184
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c10725 h a184 u0_51 u1_72 u2_105

theorem c32788 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 9} → False := by
  classical
  intro a178
  have u0_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  exact c9875 h a178 u0_51 u2_72 u1_105

end BorsukNine.FiniteObstruction

end OAI

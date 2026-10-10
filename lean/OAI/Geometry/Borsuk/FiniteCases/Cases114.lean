import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases113

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32594 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 8} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro a233 a41 a49
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32593 h h0 hv a41 a49
  have u1_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32588 h h0 u0_29 hv a41 a49
  have u2_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31919 h h0 u1_200 a41 hv
  have u3_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv u2_38
  have u4_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c12869 h u1_200 a41 hv
  have u5_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c1297 h hv u4_87
  have u6_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c14275 h u6_210 u0_29 hv
  have u8_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12984 h u1_200 hv u4_87 u7_105
  have u9_45 : T {1, 3, 5} := by
    by_contra hv
    exact c673 h a233 hv
  have u10_48 : T {1, 3, 8} := by
    by_contra hv
    exact c714 h a233 hv
  have u11_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c32225 h h0 hv u9_45 a49
  have u12_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6727 h hv u9_45 u10_48 a49
  have u13_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c32235 h h0 hv u9_45 u10_48
  have u14_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c32176 h h0 hv u10_48 a49
  exact c31226 h u11_281 u13_282 u12_156 u8_72 u14_276 u3_212 u5_262

theorem c32595 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro n101 n311 n177 a41 a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c32594 h h0 hv a41 a49
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32593 h h0 hv a41 a49
  have u3_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u4_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c14275 h u3_210 u2_29 hv
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32588 h h0 u2_29 hv a41 a49
  have u6_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c12869 h u5_200 a41 hv
  have u7_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12984 h u5_200 hv u6_87 u4_105
  have u8_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18339 h hv u2_29 u7_72
  have u9_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12982 h u5_200 hv u6_87 u4_105
  have u10_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23239 h hv u2_29 u9_51
  have u11_30 : T {0, 5, 9} := by
    by_contra hv
    exact c450 h u5_200 hv
  have u12_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u3_210 hv
  have u13_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32486 h h0 hv u12_43 a41
  have u14_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32426 h h0 hv a41 u12_43
  have u15_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32396 h h0 a41 hv u12_43
  have u16_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c31820 h h0 a41 hv u12_43
  have u17_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u3_210 hv
  have u18_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31655 h h0 n101 hv u4_105
  have u19_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31657 h h0 n101 hv u4_105
  have u20_23 : T {0, 4, 6} := by
    by_contra hv
    exact c14330 h u3_210 hv n101 u4_105
  have u21_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u18_106
  have u22_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 hv u18_106 u14_301 u16_190
  have u23_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10585 h hv u9_51 u7_72 u18_106
  have u24_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22477 h hv u20_23 u9_51 u19_107
  have u25_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c29087 h hv u20_23 u9_51 u7_72
  have u26_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1484 h hv u23_183 u8_239 u10_274 u0_304 u21_310 u25_315
  have u27_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c31560 h h0 u22_246 u16_190 hv u14_301
  have u28_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c32025 h h0 u22_246 hv u17_70
  have u29_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32591 h u24_268 u1_233 hv n311 n177 u13_307 u15_298
  have u30_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c31288 h u21_310 u23_183 u25_315 u10_274 u26_313 hv u8_239
  have u31_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c32225 h h0 u27_281 hv a49
  have u32_4 : T {0, 1, 5} := by
    by_contra hv
    exact c24204 h u27_281 hv u30_99
  have u33_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c24241 h u27_281 u32_4 hv u11_30
  have u34_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11696 h hv u31_45 u28_66 u29_93
  have u35_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19536 h hv u33_17 u28_66 u29_93
  have u36_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24436 h hv u33_17 u31_45 u29_93
  exact c31459 h h0 u36_282 u34_191 u35_247 u19_107

theorem c32596 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 5, 6} → T {4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → False := by
  classical
  intro n276 a101 n296 n185
  have u0_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c31537 h h0 hv n276 n296 n185
  exact c31261 h h0 n185 u0_241 a101 n276

theorem c32597 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 1, 2, 9} → T {1, 2, 7} → T {1, 3, 9} → False := by
  classical
  intro n311 n177 n127 a41 a49
  have u0_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c32594 h h0 hv a41 a49
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32593 h h0 hv a41 a49
  have u2_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32588 h h0 u1_29 hv a41 a49
  have u3_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31919 h h0 u2_200 a41 hv
  have u4_95 : T {3, 6, 7} := by
    by_contra hv
    exact c12864 h u2_200 u3_38 hv
  have u5_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u6_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c14275 h u5_210 u1_29 hv
  have u7_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c12869 h u2_200 a41 hv
  have u8_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12984 h u2_200 hv u7_87 u6_105
  have u9_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12982 h u2_200 hv u7_87 u6_105
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31920 h h0 u2_200 hv a41
  have u11_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u5_210 hv
  have u12_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32486 h h0 hv u11_43 a41
  have u13_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32375 h h0 a41 hv u11_43
  have u14_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32396 h h0 a41 hv u11_43
  have u15_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c31769 h h0 a41 hv u11_43
  have u16_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u5_210 hv
  have u17_101 : T {4, 5, 6} := by
    by_contra hv
    exact c32595 h h0 hv n311 n177 a41 a49
  have u18_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31628 h h0 u17_101 hv
  have u19_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c31957 h h0 hv u17_101
  have u20_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c14281 h u5_210 hv u17_101
  have u21_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10583 h hv u9_51 u8_72 u17_101
  have u22_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u15_185 hv u18_120
  have u23_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5591 h hv u22_71 u4_95
  have u24_276 : Q {2, 4, 5, 6} := by
    by_contra hv
    exact c32596 h h0 hv u17_101 u13_296 u15_185
  have u25_76 : T {2, 5, 6} := by
    by_contra hv
    exact c1134 h u24_276 hv
  have u26_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31538 h h0 u24_276 u15_185 u13_296 hv
  have u27_62 : T {1, 7, 8} := by
    by_contra hv
    exact c23620 h u24_276 u20_34 hv u18_120
  have u28_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32176 h h0 u24_276 hv a49
  have u29_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c23515 h u24_276 hv u27_62
  have u30_98 : T {3, 7, 8} := by
    by_contra hv
    exact c23622 h u24_276 u20_34 hv u18_120
  have u31_138 : ¬ Q {0, 1, 4, 9} := by
    intro hv
    exact c4191 h hv u25_76 u30_98
  have u32_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u26_241 hv
  have u33_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u26_241 hv
  have u34_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c31976 h h0 u26_241 hv u16_70
  have u35_83 : T {2, 7, 8} := by
    by_contra hv
    exact c18614 h u26_241 u29_21 hv
  have u36_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9801 h hv u27_62 u8_72
  have u37_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6441 h hv u27_62 u17_101
  have u38_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c11315 h hv u27_62 u35_83 u30_98
  have u39_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7688 h hv u28_48 u6_105
  have u40_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c303 h hv u29_21
  have u41_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c4751 h hv u8_72 u30_98
  have u42_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5171 h hv u22_71 u30_98
  have u43_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8531 h hv u32_50 u4_95
  have u44_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8111 h hv u32_50 u30_98
  have u45_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7131 h hv u33_55 u30_98
  have u46_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c1029 h hv u34_69
  have u47_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12575 h hv u27_62 u35_83 u30_98
  have u48_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c224 h hv n127 u37_154 u45_159 u39_163 u44_166 u43_169
  have u49_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c119 h hv n127 u40_133 u31_138 u41_142 u42_145 u23_148
  have u50_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32591 h u46_268 u0_233 hv n311 n177 u12_307 u14_298
  have u51_199 : Q {0, 5, 7, 9} := by
    by_contra hv
    exact c451 h u2_200 u41_142 u39_163 u36_178 u38_188 u47_197 hv
  have u52_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11886 h hv u10_40 u50_93
  have u53_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13144 h hv u3_38 u50_93
  exact c522 h u51_199 u49_147 u48_168 u21_183 u52_193 u53_202 u19_204

theorem c32598 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 7} → ¬ T {1, 2, 6} → ¬ T {1, 2, 4} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → T {1, 2, 7} → Q {1, 2, 3, 9} → False := by
  classical
  intro a311 n127 n208 n40 n38 n87 n105 a41 a210
  have u0_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c600 h hv n40
  have u1_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c596 h hv n40
  have u2_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c570 h hv n38
  have u3_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c566 h hv n38
  have u4_24 : T {0, 4, 7} := by
    by_contra hv
    exact c28418 h a311 hv n40
  have u5_31 : T {0, 6, 7} := by
    by_contra hv
    exact c28420 h a311 hv n38
  have u6_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28417 h a311 hv a41
  have u7_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28459 h a311 hv u4_24 u5_31
  have u8_114 : T {5, 7, 8} := by
    by_contra hv
    exact c14264 h a210 u6_23 hv
  have u9_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16464 h hv u6_23 n87 n105
  have u10_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15614 h hv u6_23 n87 n105
  have u11_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c78 h hv u7_6
  have u12_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u8_114
  have u13_224 : Q {1, 2, 7, 9} := by
    by_contra hv
    exact c636 h a210 n127 u2_215 u10_219 u0_222 hv u9_225
  have u14_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16184 h hv u6_23 n87 u12_107
  have u15_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15336 h hv u6_23 n87 u12_107
  exact c616 h u13_224 u11_125 n208 u3_213 u15_217 u1_220 u14_223

theorem c32599 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → False := by
  classical
  intro a177 n40
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h a177 hv
  have u2_20 : T {0, 3, 8} := by
    by_contra hv
    exact c294 h a177 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c9644 h a177 n40 hv
  have u4_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32252 h h0 hv u1_17 u2_20
  have u5_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c32052 h h0 u1_17 u2_20 hv
  have u6_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31573 h h0 hv u4_284 u5_249 u0_304
  exact c31572 h h0 u5_249 u6_193 u3_109 u0_304 u4_284

end BorsukNine.FiniteObstruction

end OAI

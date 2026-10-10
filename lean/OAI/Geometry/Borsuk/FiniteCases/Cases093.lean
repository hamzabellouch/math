import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases092

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31455 (h : TenSystem T Q) :
    T {1, 5, 7} → T {1, 7, 8} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → T {0, 2, 6} → T {1, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro a56 a62 n13 n304 a12 a59 a230
  have u0_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26731 h hv a12 a62
  have u1_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv a12 a56
  have u2_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9273 h hv a56 a59 a62
  have u3_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22045 h hv a56 a59 a62
  have u4_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1341 h a230 u2_174 u3_265 u0_299 hv n304 u1_305
  have u5_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c27155 h u4_302 hv a56
  have u6_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c27151 h u4_302 hv a62
  exact c27176 h u4_302 u6_11 n13 u5_14

private theorem c31457 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 7} → T {0, 2, 9} → ¬ Q {3, 5, 8, 9} → T {4, 5, 7} → ¬ Q {3, 6, 8, 9} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → ¬ T {4, 6, 7} → T {0, 2, 6} → T {1, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro a56 a15 n311 a102 n314 n13 n304 n105 a12 a59 n201 n195 n292 n286 a230 n240
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv a12 a56
  have u7_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h a56 hv n13 n304 a12 a59 a230
  have u8_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u7_62
  have u9_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u8_257 n292 u2_322 u1_326 u0_330
  have u10_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u8_257 n292 u9_312 u2_322 u1_326 u0_330
  have u11_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u10_117
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u3_121 n105 hv u10_117
  have u13_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28995 h hv u4_1 u11_11 a12
  have u14_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u12_111 hv n195
  have u15_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10751 h hv a56 a102 u12_111
  have u16_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23493 h hv a56 a102 u12_111
  have u17_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c20025 h u14_251 u5_9 hv a15
  have u18_100 : T {3, 8, 9} := by
    by_contra hv
    exact c20004 h u14_251 u17_10 hv
  exact c1487 h u18_100 u15_184 n240 u16_275 u6_305 n311 n314 u13_315

theorem c31458 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 6, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro a166 n311 n114 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u0_121 hv n114
  have u2_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 n103 hv
  have u4_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u5_33 : T {0, 6, 9} := by
    by_contra hv
    exact c485 h a166 hv
  have u6_82 : T {2, 6, 9} := by
    by_contra hv
    exact c1218 h a166 hv
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c8232 h a166 hv n103 n114
  have u8_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17611 h hv u5_33 u1_107 u3_118
  have u9_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22511 h hv u5_33 u1_107 u3_118
  have u10_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9773 h hv u6_82 u1_107 u3_118
  have u11_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv u10_177 u8_233 u9_268 u4_298 u2_309 n311
  exact c1382 h u7_93 u10_177 u8_233 u9_268 u4_298 u11_307 u2_309 n311

theorem c31459 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → T {4, 6, 9} → False := by
  classical
  intro n282 n191 n247 a107
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1592 h a107 n191 n247 n282 hv u0_318 u1_323 u2_324
  exact c1600 h u3_302 n191 n247 n282 u0_318 u1_323 u2_324

theorem c31460 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 5, 7} → ¬ T {5, 7, 8} → ¬ Q {1, 4, 6, 9} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n56 n114 n247 n195 n286 a230
  have u0_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u6_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv n114
  have u7_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u8_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u9_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c832 h hv n56
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c836 h hv n56
  have u11_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1660 h hv n195 u10_251 n286 u2_316 u1_326 u0_327
  have u12_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u10_251 n195
  have u13_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u3_121 hv u12_111
  have u14_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u12_111
  have u15_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22357 h hv u8_54 u6_107 u13_110
  have u16_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9615 h hv u8_54 u6_107 u13_110
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28295 h hv u4_1 u5_12 u14_14
  have u18_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26471 h hv u4_1 u5_12 u14_14
  have u19_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c1367 h hv u16_176 u9_232 u15_267 u18_297 u11_306 u7_309 u17_310
  have u20_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24464 h hv n56 u19_92 n114
  have u21_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11722 h hv n56 u19_92 n114
  exact c31459 h h0 u20_282 u21_191 n247 u6_107

theorem c31461 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 6} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n51 n46 n103 n237 n198 n201 n195 n292 n289 n286 a230 n240 n210
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8386 h hv n46 n103
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u3_121 n103 hv
  have u7_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u8_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv n51
  have u9_59 : T {1, 6, 7} := by
    by_contra hv
    exact c31449 h h0 hv n51 n46 n103 n198 n201 n195 n292 n289 n286 a230
  have u10_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31454 h h0 hv u9_59 n51 u5_168 n103 n237 n198 n289 a230 n240 n210
  have u11_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv u10_114
  have u12_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u3_121 n103 u10_114 hv
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u3_121 n103 hv u10_114
  have u14_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u10_114
  have u15_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u3_121 u11_107 hv u6_118
  have u16_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u3_121 u11_107 u6_118 hv
  have u17_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u3_121 hv u12_116
  have u18_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27423 h hv u4_1 u13_112
  have u19_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv u13_112
  have u20_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv u19_13 u15_113
  have u21_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv u16_119
  have u22_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u3_121 hv u16_119
  have u23_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28414 h hv u19_13 n51
  have u24_56 : T {1, 5, 7} := by
    by_contra hv
    exact c31460 h h0 hv u10_114 u8_247 n195 n286 a230
  have u25_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv u14_12 u24_56
  have u26_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h u24_56 hv u19_13 u18_304 u14_12 u9_59 a230
  have u27_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c31457 h h0 u24_56 hv u23_311 u22_102 u21_314 u19_13 u18_304 u17_105 u14_12 u9_59 n201 n195 n292 n286 a230 n240
  have u28_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u26_62
  have u29_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u28_257 n292 u2_322 u1_326 u0_330
  have u30_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u28_257 n292 u29_312 u2_322 u1_326 u0_330
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u30_117
  have u32_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u3_121 u17_105 hv u30_117
  have u33_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27311 h hv u4_1 u31_11 u14_12
  have u34_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u32_111 hv n195
  have u35_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21945 h hv u9_59 u32_111 u6_118
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9203 h hv u9_59 u32_111 u6_118
  have u37_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u36_173 u20_229 u35_264 u7_298 u33_303 u25_305
  have u38_89 : T {3, 4, 8} := by
    by_contra hv
    exact c20008 h u34_251 u27_15 hv
  exact c1322 h u38_89 u36_173 u20_229 u35_264 u7_298 u37_301 u33_303 u25_305

theorem c31462 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 6, 7} → T {1, 5, 7} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → T {5, 8, 9} → ¬ T {5, 7, 8} → T {1, 4, 6} → T {6, 7, 9} → ¬ Q {3, 4, 5, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro a59 a56 n165 n160 n13 n304 a116 n114 a51 a118 n298 n201 n292 a230 n240
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u4_121 hv n114
  have u6_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6293 h hv a56 u5_107
  have u7_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u8_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv u7_12 a56
  have u9_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u4_121 u5_107 a118 hv
  have u10_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv u9_119
  have u11_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv u9_119
  have u12_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u4_121 u5_107 hv a118
  have u13_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv n13 u12_113
  have u14_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6145 h hv a51 a116
  have u15_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u16_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7823 h hv u15_44 a116
  have u17_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u4_121 hv a116
  have u18_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u19_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u20_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5731 h hv a59 a116
  have u21_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h a56 hv n13 n304 u7_12 a59 a230
  have u22_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c922 h hv u21_62
  have u23_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u21_62
  have u24_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u23_257 n292 u2_322 u1_326 u0_330
  have u25_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u23_257 n292 u24_312 u2_322 u1_326 u0_330
  have u26_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u4_121 hv u25_117
  have u27_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u25_117
  have u28_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1924 h u4_121 n114 u25_117 hv
  have u29_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u4_121 u17_105 hv u25_117
  have u30_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6558 h hv u21_62 n114 u25_117
  have u31_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10455 h hv u19_54 u26_104 u5_107
  have u32_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23197 h hv u19_54 u26_104 u5_107
  have u33_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28995 h hv u3_1 u27_11 u7_12
  have u34_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27311 h hv u3_1 u27_11 u7_12
  have u35_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv a51 u28_120
  have u36_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21945 h hv a59 u29_111 a118
  have u37_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9203 h hv a59 u29_111 a118
  have u38_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10751 h hv a56 u10_102 u29_111
  have u39_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23493 h hv a56 u10_102 u29_111
  have u40_98 : ¬ T {3, 7, 8} := by
    intro hv
    exact c1457 h hv u31_182 u22_238 u32_273 u34_303 u18_309 u24_312 u33_315
  have u41_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1497 h hv u38_184 n240 u39_275 u8_305 u11_314 u33_315
  have u42_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u37_173 u13_229 u36_264 n298 u34_303 u8_305
  have u43_151 : Q {0, 2, 3, 6} := by
    by_contra hv
    exact c124 h u4_121 u20_149 u35_150 hv u14_152 u6_153 u30_154
  have u44_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c1322 h hv u37_173 u13_229 u36_264 n298 u42_301 u34_303 u8_305
  have u45_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u38_184 n240 u39_275 u8_305 u41_311 u11_314 u33_315
  have u46_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2270 h hv u44_89 u40_98 u45_100
  have u47_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6818 h hv u21_62 u40_98 n114
  have u48_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8236 h hv u21_62 u40_98 n114
  exact c171 h u43_151 u46_124 u47_156 n160 u16_164 n165 u48_166

end BorsukNine.FiniteObstruction

end OAI

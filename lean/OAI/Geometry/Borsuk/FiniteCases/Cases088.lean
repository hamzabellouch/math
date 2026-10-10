import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases085
import OAI.Geometry.Borsuk.FiniteCases.Cases087

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31405 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a234 n237 n230 n240 a49 n210
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u6_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u7_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u8_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u9_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u10_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u11_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11493 h hv u1_37 u8_45 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24125 h hv u0_2 u8_45 a49
  have u13_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24265 h hv u0_2 u8_45 a49
  have u14_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25807 h hv u0_2 u8_45 a49
  have u15_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24545 h hv u0_2 u8_45 a49
  have u16_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11773 h hv u1_37 u8_45 a49
  have u17_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31398 h h0 hv a234
  have u18_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c730 h a234 hv n210 n230 n237 u17_239 n240
  have u19_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31401 h h0 hv u18_133 u16_192 u14_292 u12_280 u11_190 a234
  have u20_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u2_121 u19_108 hv
  have u21_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u19_108
  have u22_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h u18_133 hv u19_108
  have u23_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7091 h hv u9_58 u10_94 u20_113
  have u24_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31404 h h0 hv u19_108 u18_133 u16_192 u11_190 a234
  have u25_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u2_121 u24_106 hv
  have u26_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1852 h u2_121 u24_106 u19_108 hv
  have u27_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv u24_106
  have u28_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h u18_133 hv u24_106
  have u29_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21937 h hv u9_58 u20_113 u25_115
  have u30_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14937 h hv u10_94 u20_113 u25_115
  have u31_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27595 h hv u3_1 u21_12 u27_13
  have u32_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19887 h hv u4_9 u21_12 u27_13
  have u33_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c3511 h u18_133 hv u22_76 u28_77
  have u34_194 : Q {0, 4, 8, 9} := by
    by_contra hv
    exact c31402 h h0 u32_250 u26_110 u31_305 hv
  have u35_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c1063 h hv u33_71
  have u36_285 : Q {2, 4, 8, 9} := by
    by_contra hv
    exact c1639 h u34_194 u32_250 hv u31_305 u7_321 u6_324 u5_325
  exact c1111 h u36_285 u23_158 u30_214 u29_264 u35_278 u13_281 u15_283

private theorem c31406 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 8, 9} → ¬ T {0, 5, 6} → Q {1, 3, 7, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a194 n27 a239 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u3_36 : T {0, 8, 9} := by
    by_contra hv
    exact c534 h a194 hv
  have u4_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c12053 h a194 u0_37 hv u2_47
  have u5_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c12055 h a194 u0_37 hv u2_47
  have u6_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c12035 h a194 u2_47 hv
  have u7_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c665 h hv u4_45
  have u8_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c680 h hv u5_46
  have u9_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18438 h a239 n27 u6_76 hv
  have u10_112 : T {5, 6, 8} := by
    by_contra hv
    exact c18440 h a239 n27 u6_76 hv
  have u11_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u9_101 hv
  have u12_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14001 h hv u3_36 u9_101
  have u13_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u1_121 hv u10_112
  have u14_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13562 h hv n27 u11_120
  have u15_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c544 h u1_121 u14_205 u7_206 u8_207 u12_208 hv n210
  exact c14130 h u15_209 n27 u13_109

private theorem c31407 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 5, 6} → ¬ Q {0, 4, 8, 9} → ¬ T {0, 5, 6} → T {4, 8, 9} → False := by
  classical
  intro n76 n194 n27 a110
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u2_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27682 h hv n27 n76 u1_111
  have u3_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19980 h hv n27 n76 u1_111
  exact c31402 h h0 u3_250 a110 u2_305 n194

private theorem c31408 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {1, 3, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ T {0, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ T {5, 6, 7} → T {0, 3, 9} → T {3, 7, 9} → False := by
  classical
  intro a305 n231 n139 n27 n251 n111 a21 a99
  have u0_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h a305 hv
  have u1_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1494 h a305 hv
  have u2_55 : T {1, 5, 6} := by
    by_contra hv
    exact c27680 h a305 n27 hv n111
  have u3_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15187 h hv a21 u0_90 a99
  have u4_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20255 h hv a21 u0_90 a99
  have u5_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18715 h hv a21 a99 u1_100
  have u6_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c826 h hv n139 u3_216 n231 u5_241 n251 u4_252
  exact c812 h u2_55 n139 u3_216 n231 u5_241 n251 u4_252 u6_253

private theorem c31409 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 6} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ T {0, 5, 6} → T {4, 8, 9} → T {0, 3, 9} → T {0, 1, 9} → T {3, 7, 9} → T {1, 7, 9} → False := by
  classical
  intro n231 n194 n139 n175 n27 a110 a21 a8 a99 a63
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20003 h hv u2_9 a110
  have u4_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27703 h hv u1_1 a110
  have u5_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31408 h hv n231 n139 n27 u3_251 u5_111 a21 a99
  have u7_250 : Q {1, 4, 8, 9} := by
    by_contra hv
    exact c31402 h h0 hv a110 u6_305 n194
  have u8_54 : T {1, 4, 9} := by
    by_contra hv
    exact c810 h u7_250 hv
  have u9_64 : T {1, 8, 9} := by
    by_contra hv
    exact c954 h u7_250 hv
  have u10_91 : T {3, 5, 6} := by
    by_contra hv
    exact c19982 h u7_250 n27 hv u5_111
  have u11_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22193 h hv u8_54 a63 u9_64
  have u12_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27931 h hv a8 u8_54 a63
  have u13_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26391 h hv a8 a63 u9_64
  have u14_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1366 h hv n175 n231 u11_266 u13_296 u4_306 u12_307
  exact c1352 h u10_91 n175 n231 u11_266 u13_296 u4_306 u12_307 u14_308

theorem c31410 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 8, 9} → Q {0, 1, 3, 9} → Q {1, 3, 7, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a110 a133 a239 a49 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u3_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h a133 hv
  have u4_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1475 h a239 hv
  have u5_63 : T {1, 7, 9} := by
    by_contra hv
    exact c937 h a239 hv
  have u6_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u7_74 : T {2, 4, 8} := by
    by_contra hv
    exact c3488 h a133 hv u6_111
  have u8_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c18337 h a239 hv u7_74
  have u9_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9379 h hv u5_63 u7_74
  have u10_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4333 h hv u7_74 u4_99
  have u11_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c31406 h h0 hv u8_27 a239 n210
  have u12_76 : T {2, 5, 6} := by
    by_contra hv
    exact c31407 h h0 hv u11_194 u8_27 a110
  have u13_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11755 h hv a49 u12_76
  have u14_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c3491 h a133 u12_76 hv
  have u15_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u0_121 u14_108 hv
  have u16_231 : Q {1, 3, 5, 6} := by
    by_contra hv
    exact c31409 h h0 hv u11_194 u10_139 u9_175 u8_27 a110 u2_21 u3_8 u4_99 u5_63
  have u17_45 : T {1, 3, 5} := by
    by_contra hv
    exact c669 h u16_231 hv
  have u18_46 : T {1, 3, 6} := by
    by_contra hv
    exact c684 h u16_231 hv
  have u19_55 : T {1, 5, 6} := by
    by_contra hv
    exact c817 h u16_231 hv
  have u20_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1355 h u16_231 hv
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17205 h u16_231 hv a110
  have u22_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c17219 h u16_231 hv u7_74
  have u23_24 : T {0, 4, 7} := by
    by_contra hv
    exact c17240 h u16_231 u21_13 hv u22_35
  have u24_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11353 h hv u1_37 u17_45 a49
  have u25_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u18_46 a49
  have u26_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11911 h hv u1_37 u17_45 u18_46
  have u27_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6865 h hv u17_45 u18_46 a49
  have u28_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9037 h hv u19_55 u12_76 u15_113
  have u29_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3997 h hv u12_76 u20_91 u15_113
  exact c347 h u23_24 u29_136 u27_157 u28_172 u25_186 u24_189 u13_192 u26_193

theorem c31412 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 1, 5, 6} → T {0, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → Q {0, 1, 3, 9} → False := by
  classical
  intro n76 n175 n139 a27 n185 n196 a133
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c1128 h hv n76
  have u2_108 : T {4, 7, 8} := by
    by_contra hv
    exact c3490 h a133 n76 hv
  have u3_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12443 h hv u0_37 u2_108
  have u4_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c402 h hv n139 u1_160 n175 n185 n196 u3_197
  exact c392 h a27 n139 u1_160 n175 n185 u4_195 n196 u3_197

theorem c31419 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 5, 6} → ¬ T {4, 8, 9} → T {0, 1, 9} → ¬ Q {2, 4, 6, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → False := by
  classical
  intro a139 n110 a8 n281 n187 n278 n190
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_4 : T {0, 1, 5} := by
    by_contra hv
    exact c54 h a139 hv
  have u8_5 : T {0, 1, 6} := by
    by_contra hv
    exact c69 h a139 hv
  have u9_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27025 h hv u0_1 u7_4 a8
  have u10_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26605 h hv u0_1 u8_5 a8
  have u11_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c1581 h hv n190 n281 u9_301 u5_317 u2_322 u1_324
  have u12_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c1536 h hv n187 n278 u10_298 u5_317 u4_319 u3_321
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31307 h h0 u11_246 hv u9_301 n190
  have u14_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1532 h hv n187 u12_243 n278 u10_298 u5_317 u4_319 u3_321
  exact c1848 h u6_121 u14_103 u13_106 n110

end BorsukNine.FiniteObstruction

end OAI

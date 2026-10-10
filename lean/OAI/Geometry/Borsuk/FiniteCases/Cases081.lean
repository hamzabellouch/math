import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases068
import OAI.Geometry.Borsuk.FiniteCases.Cases080

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31248 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 7} → ¬ T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 3, 4, 5} → False := by
  classical
  intro a6 n3 a315 n22 n170
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := h0
  have u3_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u4_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u7_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u7_40
  have u9_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 n3 u8_38 hv
  have u10_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u9_51 u6_120
  have u11_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u8_38
  have u12_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 n3 hv
  have u13_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u11_27 hv u12_76
  have u14_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u15_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u14_101
  have u16_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u15_71
  have u17_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 n3 hv u16_5
  have u18_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 n3 hv n22
  have u19_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u7_40
  have u20_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u19_39
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 u12_76
  have u22_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 u15_71
  have u23_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26047 h hv u1_2 u17_4 a6
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31247 h h0 hv a6 n3 a315 n22 n170
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u2_121 u24_102 hv
  have u26_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1822 h u2_121 u14_101 u24_102 hv
  have u27_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1824 h u2_121 u14_101 u24_102 hv
  have u28_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23366 h hv u16_5 u24_102
  have u29_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u14_101 u24_102
  have u30_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u2_121 hv u25_119 u6_120
  have u31_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u2_121 hv u25_119 u6_120
  have u32_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21405 h hv a6 u25_119
  have u33_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u26_103 hv
  have u34_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u2_121 u27_104 hv
  have u35_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22244 h hv u16_5 u30_110
  have u36_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv u31_116
  have u37_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22382 h hv n3 u33_118
  have u38_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22522 h hv n3 u34_117
  have u39_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv u29_240 u28_275 u21_305 u36_311 u22_314
  have u40_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c985 h hv u10_150 u20_206 u32_261 u35_267 u37_268 u38_269
  have u41_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c10635 h u39_184 hv u12_76
  have u42_73 : T {2, 4, 7} := by
    by_contra hv
    exact c10636 h u39_184 u13_55 hv
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u10_150 u20_206 u32_261 u40_266 u35_267 u37_268 u38_269
  have u44_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13298 h hv u41_52 u43_66
  have u45_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21195 h hv u18_10 u15_71 u42_73
  exact c1772 h u25_119 u44_203 u45_259 u23_294 u22_314 u5_324 u4_328 u3_330

private theorem c31249 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 6, 8, 9} → ¬ T {2, 3, 5} → ¬ Q {1, 3, 8, 9} → T {6, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ T {2, 4, 6} → ¬ T {1, 5, 6} → T {0, 1, 5} → T {0, 2, 4} → T {2, 5, 6} → T {2, 4, 5} → T {1, 4, 5} → Q {3, 7, 8, 9} → False := by
  classical
  intro n314 n66 n240 a119 n311 n275 n72 n55 a4 a10 a76 a71 a50 a315
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u5_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u0_121 hv a119 u4_120
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1644 h hv u5_110
  have u7_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv n240 n275 u6_305 n311 n314
  have u8_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c10635 h u7_184 hv a76
  have u9_73 : T {2, 4, 7} := by
    by_contra hv
    exact c10636 h u7_184 n55 hv
  have u10_56 : T {1, 5, 7} := by
    by_contra hv
    exact c10638 h u7_184 hv n72
  have u11_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13298 h hv u8_52 n66
  have u12_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21195 h hv a10 a71 u9_73
  have u13_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26103 h hv a4 a50 u10_56
  exact c1772 h a119 u11_203 u12_259 u13_294 n314 u3_324 u2_328 u1_330

private theorem c31250 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n102 a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u3_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u2_101
  have u4_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u3_71
  have u5_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c318 h hv n22
  have u6_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u7_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31244 h h0 hv a315 n22 u6_186 u5_134
  have u8_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c322 h hv n22
  have u9_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c31248 h h0 hv u7_3 a315 n22 u8_170
  have u10_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28428 h hv u7_3 u4_5 u9_6
  have u11_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22542 h hv u7_3 u4_5 u9_6
  have u12_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22402 h hv u7_3 u4_5 u9_6
  have u13_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv u9_6 u2_101
  have u14_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c80 h hv u9_6
  have u15_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u16_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u17_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u16_40
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 u7_3 u17_38 hv
  have u19_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u18_51 u15_120
  have u20_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 u7_3 hv n22
  have u21_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17203 h hv u20_10 u15_120
  have u22_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 u7_3 hv
  have u23_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c29067 h a315 hv u3_71 u22_76
  have u24_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u16_40 hv u22_76
  have u25_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u17_38
  have u26_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u25_27 hv u22_76
  have u27_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u16_40
  have u28_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u27_39
  have u29_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 u7_3 hv u4_5
  have u30_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29002 h a315 u7_3 n22 hv
  have u31_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u7_3
  have u32_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u3_71 u15_120
  have u33_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26303 h hv u0_1 u15_120
  have u34_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u2_101
  have u35_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1524 h hv n102
  have u36_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 n102 hv
  have u37_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u2_101 n102
  have u38_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u1_121 hv u36_119 u15_120
  have u39_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17343 h hv u20_10 u36_119
  have u40_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22244 h hv u4_5 u38_110
  have u41_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22104 h hv u9_6 u38_110
  have u42_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c983 h hv u19_150 u28_206 u41_266 u40_267 u12_268 u11_269
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u19_150 u28_206 u42_261 u41_266 u40_267 u12_268 u11_269
  have u44_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31249 h h0 hv u43_66 u37_240 u36_119 u10_311 u13_275 u24_72 u26_55 u29_4 u20_10 u22_76 u3_71 u34_50 a315
  have u45_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28836 h u44_314 n22 hv
  have u46_24 : T {0, 4, 7} := by
    by_contra hv
    exact c28838 h u44_314 hv u27_39
  have u47_77 : T {2, 5, 7} := by
    by_contra hv
    exact c28924 h u44_314 u23_11 u27_39 hv
  have u48_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26783 h hv u0_1 u16_40 u45_41
  have u49_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26643 h hv u0_1 u16_40 u45_41
  have u50_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17511 h hv u20_10 u30_23 u46_24
  have u51_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17651 h hv u20_10 u30_23 u46_24
  have u52_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3511 h hv u3_71 u22_76 u47_77
  have u53_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3371 h hv u3_71 u22_76 u47_77
  have u54_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c1281 h hv u8_170 u42_261 u33_296 u35_297 u49_298 u48_299
  have u55_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c664 h hv u28_206 u54_226 u21_231 u39_232 u50_233 u51_234
  exact c19 h u1_121 u31_128 u55_129 u32_130 u14_131 u53_132 u52_133

private theorem c31251 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 8, 9} → ¬ Q {2, 3, 5, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {2, 3, 4, 6} → T {0, 5, 6} → ¬ Q {1, 2, 3, 4} → T {0, 1, 5} → T {0, 4, 6} → ¬ T {0, 2, 6} → ¬ Q {0, 2, 3, 6} → ¬ T {1, 2, 5} → T {1, 4, 5} → False := by
  classical
  intro a305 n266 n208 n262 a27 n205 a4 a23 n12 n151 n39 a50
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv n39
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1644 h a305 hv
  have u3_56 : T {1, 5, 7} := by
    by_contra hv
    exact c27572 h a305 n12 hv
  have u4_31 : T {0, 6, 7} := by
    by_contra hv
    exact c27580 h a305 hv n39
  have u5_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22665 h hv a4 u2_110
  have u6_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22871 h hv a4 a50 u3_56
  have u7_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23011 h hv a4 a50 u3_56
  have u8_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14159 h hv a23 a27 u4_31
  have u9_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14299 h hv a23 a27 u4_31
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c996 h hv n151 n262 n266 u5_270 u6_271 u7_272
  exact c544 h u0_121 n205 u1_206 u10_207 n208 u8_209 u9_210

theorem c31252 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u6_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c322 h hv n22
  have u7_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c318 h hv n22
  have u8_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u9_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u10_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u11_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u9_101
  have u12_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u9_101
  have u13_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31244 h h0 hv a315 n22 u5_186 u7_134
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u10_40
  have u15_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u10_40
  have u16_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u11_50 u8_120
  have u17_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u11_50
  have u18_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u12_71
  have u19_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 u13_3 hv
  have u20_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 u13_3 hv n22
  have u21_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29002 h a315 u13_3 n22 hv
  have u22_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 u13_3 u14_38 hv
  have u23_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 u13_3 hv u18_5
  have u24_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c31248 h h0 hv u13_3 a315 n22 u6_170
  have u25_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u14_38
  have u26_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u14_38
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u15_39
  have u28_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u10_40 hv u19_76
  have u29_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u22_51 u8_120
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21543 h hv u23_4 u8_120
  have u31_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv u24_6 u9_101
  have u32_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22402 h hv u13_3 u18_5 u24_6
  have u33_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22542 h hv u13_3 u18_5 u24_6
  have u34_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28428 h hv u13_3 u18_5 u24_6
  have u35_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31250 h h0 hv a315 n22
  have u36_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u1_121 u35_102 hv
  have u37_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28823 h hv u0_1 u35_102
  have u38_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u10_40 u35_102
  have u39_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22242 h hv u13_3 u36_119
  have u40_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv u24_6 u36_119
  have u41_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u36_119
  have u42_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c985 h hv u29_150 u27_206 u40_261 u39_267 u32_268 u33_269
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u29_150 u27_206 u40_261 u42_266 u39_267 u32_268 u33_269
  have u44_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31251 h h0 hv u42_266 u41_208 u30_262 u26_27 u25_205 u23_4 u21_23 u17_12 u16_151 u15_39 u11_50
  have u45_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u38_184 hv u31_275 u44_305 u34_311 u37_314
  have u46_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c18463 h u45_240 u20_10 hv
  have u47_28 : T {0, 5, 7} := by
    by_contra hv
    exact c18478 h u45_240 hv u28_72
  have u48_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c18481 h u45_240 hv u12_71
  have u49_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18537 h u45_240 u12_71 u19_76 hv
  have u50_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u1_121 hv u46_111
  have u51_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24803 h hv u23_4 u26_27 u47_28
  have u52_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19880 h hv u48_31 u43_66
  have u53_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12092 h hv u15_39 u43_66 u49_77
  exact c1637 h u50_110 u53_194 u52_250 u51_285 u44_305 u4_321 u3_324 u2_325

end BorsukNine.FiniteObstruction

end OAI

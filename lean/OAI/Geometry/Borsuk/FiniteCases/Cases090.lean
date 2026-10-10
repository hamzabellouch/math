import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases086
import OAI.Geometry.Borsuk.FiniteCases.Cases089

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31428 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ Q {2, 5, 8, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 4, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {0, 3, 5, 7} → ¬ Q {1, 2, 5, 9} → ¬ T {1, 7, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 5, 6, 9} → ¬ T {3, 7, 9} → ¬ Q {2, 5, 6, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 5, 7} → False := by
  classical
  intro n106 n291 n279 n185 n196 n140 n216 n287 n276 n139 n266 n176 n219 n63 n269 n155 n162 n163 n175 n197 n99 n286 n161 n198 n186
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1481 h hv n99
  have u2_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u0_121 n106 hv
  have u3_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2098 h hv n99 n106
  have u4_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5878 h hv n63 n106
  have u5_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c160 h hv u3_123 u4_150 n155 n161 n162 n163
  have u6_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u5_160 n216 n266 n276 n286 n287
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c402 h hv n139 u5_160 n175 n185 n196 n197
  have u8_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c1184 h hv n163 n219 n269 n279 u6_288 n291
  have u9_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c421 h hv n140 n161 n176 n186 u7_195 n198
  exact c31335 h h0 u2_115 u1_310 u8_290 u9_199

private theorem c31429 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a103 a133 n198 n278 n187 n186 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u7_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h a133 hv
  have u8_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u9_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u10_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u11_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u12_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv a103
  have u13_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h a133 hv a103
  have u14_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv a103 n187 n278
  have u15_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c189 h hv u12_13
  have u16_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1196 h hv u13_80
  have u17_68 : T {2, 3, 7} := by
    by_contra hv
    exact c18958 h u14_243 u12_13 hv u13_80
  have u18_84 : T {2, 7, 9} := by
    by_contra hv
    exact c18962 h u14_243 u12_13 u13_80 hv
  have u19_95 : T {3, 6, 7} := by
    by_contra hv
    exact c19004 h u14_243 u13_80 hv u11_118
  have u20_53 : T {1, 4, 8} := by
    by_contra hv
    exact c789 h u14_243 hv
  have u21_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c18995 h u14_243 u6_21 u8_97 hv
  have u22_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18991 h u14_243 u6_21 hv u8_97
  have u23_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u14_243 n187 n278 hv u3_317 u2_319 u1_321
  have u24_31 : T {0, 6, 7} := by
    by_contra hv
    exact c19000 h u14_243 hv u13_80 u11_118
  have u25_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c18915 h u14_243 u4_9 hv u6_21
  have u26_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c18943 h u14_243 u4_9 hv u17_68
  have u27_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12459 h hv u20_53 u17_68
  have u28_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9373 h hv u20_53 u18_84
  have u29_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c26585 h u23_298 hv u18_84
  have u30_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7695 h hv u20_53 u19_95
  have u31_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7615 h hv u10_46 u19_95 u8_97
  have u32_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6625 h hv u10_46 u19_95 u8_97
  have u33_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c18889 h u14_243 hv u19_95
  have u34_35 : T {0, 7, 9} := by
    by_contra hv
    exact c19018 h u14_243 hv u21_99 u11_118
  have u35_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c1044 h hv u22_70
  have u36_82 : T {2, 6, 9} := by
    by_contra hv
    exact c18966 h u14_243 u33_15 u22_70 hv
  have u37_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1329 h u23_298 hv
  have u38_63 : ¬ T {1, 7, 9} := by
    intro hv
    exact c26671 h u23_298 u7_8 u9_61 hv
  have u39_41 : T {1, 2, 7} := by
    by_contra hv
    exact c26682 h u23_298 u12_13 hv u13_80
  have u40_59 : T {1, 6, 7} := by
    by_contra hv
    exact c26704 h u23_298 hv u13_80 u11_118
  have u41_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15537 h hv u24_31 u37_89
  have u42_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c279 h hv u25_19
  have u43_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c999 h hv u26_67
  have u44_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c69 h hv u29_5
  have u45_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23555 h hv u7_8 u6_21 u34_35
  have u46_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25097 h hv u7_8 u6_21 u34_35
  have u47_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15119 h hv u34_35 u37_89
  have u48_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4479 h hv u36_82 u37_89
  have u49_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12381 h hv u39_41 u17_68 u18_84
  have u50_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10833 h hv u39_41 u17_68 u18_84
  have u51_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c24039 h hv u24_31 u40_59 u19_95
  have u52_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25735 h hv u24_31 u40_59 u19_95
  have u53_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31428 h h0 hv u52_291 u51_279 u50_185 u49_196 u48_140 u47_216 u46_287 u45_276 u44_139 u43_266 u42_176 u41_219 u38_63 u35_269 u32_155 u31_162 u30_163 u28_175 u27_197 u21_99 u16_286 u15_161 n198 n186
  have u54_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u5_37 u53_106
  have u55_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3567 h a133 hv a103 u53_106
  have u56_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c417 h hv u48_140 u15_161 u42_176 n186 n198 u54_199
  have u57_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c407 h hv u48_140 u15_161 u42_176 n186 u56_195 n198 u54_199
  exact c18056 h a237 u57_28 u55_74

private theorem c31430 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 7} → ¬ T {2, 3, 9} → T {4, 6, 8} → Q {0, 1, 3, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n28 n70 a106 a133 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c3493 h a133 hv a106
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19316 h hv n28 n70
  have u7_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27122 h hv n28 u4_77 u5_115
  have u8_102 : T {4, 5, 7} := by
    by_contra hv
    exact c18158 h a237 n28 u4_77 hv
  have u9_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 u6_246 a106 u7_301 hv
  have u10_81 : ¬ T {2, 6, 8} := by
    intro hv
    exact c3499 h a133 hv u8_102
  have u11_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1579 h u9_190 u6_246 hv u7_301 u3_317 u2_322 u1_324
  exact c1209 h u11_281 u10_81

theorem c31431 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 4, 7, 8} → T {0, 4, 8} → ¬ Q {0, 2, 4, 8} → False := by
  classical
  intro n173 n137 n187 n194 n192 a25 n158
  have u0_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c362 h a25 n137 n158 n173 n187 hv n192 n194
  exact c372 h u0_190 n137 n158 n173 n187 n192 n194

private theorem c31432 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 7} → T {0, 4, 8} → ¬ Q {0, 2, 4, 8} → T {2, 6, 7} → T {6, 7, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro a111 a25 n158 a80 a118 n192 n187
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12023 h hv u0_37 a111
  have u2_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv a80 a111 a118
  have u3_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv a80 a111 a118
  exact c31431 h u3_173 u2_137 n187 u1_194 n192 a25 n158

private theorem c31433 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {2, 6, 7} → T {6, 7, 9} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a106 a80 a118 a133 n192 n187 n186 n277 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u2_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u3_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7109 h hv u1_61 u2_97 a118
  have u4_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c3493 h a133 hv a106
  have u7_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18054 h a237 hv u6_77
  have u8_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31432 h h0 hv u7_25 u3_158 a80 a118 n192 n187
  have u9_74 : T {2, 4, 8} := by
    by_contra hv
    exact c3488 h a133 hv u8_111
  have u10_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1872 h u0_121 hv u8_111 u5_115
  have u11_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c18057 h a237 hv u9_74
  have u12_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv n277 u10_102 n186
  have u13_70 : T {2, 3, 9} := by
    by_contra hv
    exact c31430 h h0 u11_28 hv a106 a133 a237
  exact c18851 h u12_242 u4_21 u13_70 u2_97

theorem c31434 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a133 n192 n198 n278 n187 n186 n277 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u2_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31429 h h0 hv a133 n198 n278 n187 n186 a237
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 u2_103 hv
  have u4_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv u2_103
  have u5_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u2_103
  have u6_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31433 h h0 hv u5_80 u3_118 a133 n192 n187 n186 n277 a237
  have u7_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv u6_106
  have u8_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u2_103 u6_106 hv
  have u9_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12033 h hv u1_46 u7_77
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u4_13 u7_77 u5_80
  have u11_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u4_13 u7_77 u5_80
  exact c31402 h h0 u11_250 u8_110 u10_305 u9_194

theorem c31435 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → T {2, 5, 7} → Q {1, 3, 5, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n103 a77 a234 a237
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c18055 h a237 hv a77
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c17634 h a234 u2_25 hv
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u5_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u6_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12051 h hv u0_37 u5_45 u4_46
  have u7_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u8_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c17627 h a234 u7_13 hv
  have u9_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u7_13 a77 u3_80
  have u10_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u7_13 a77 u3_80
  have u11_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u1_121 n103 u8_106 hv
  exact c31402 h h0 u10_250 u11_110 u9_305 u6_194

theorem c31436 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → Q {1, 3, 5, 9} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → Q {1, 3, 6, 9} → False := by
  classical
  intro a103 a234 n278 n187 a237
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u6_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u7_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u8_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u9_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u10_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u11_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26227 h hv u1_2 u10_45 u9_46
  have u12_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13455 h hv u0_37 u10_45 u9_46
  have u13_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u5_121 a103 hv
  have u14_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv a103
  have u15_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv a103 n187 n278
  have u16_106 : T {4, 6, 8} := by
    by_contra hv
    exact c17626 h a234 u14_13 hv
  have u17_50 : T {1, 4, 5} := by
    by_contra hv
    exact c748 h u15_243 hv
  have u18_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u15_243 n187 n278 hv u4_317 u3_319 u2_321
  have u19_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u5_121 u16_106 hv
  have u20_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1847 h u5_121 a103 u16_106 hv
  have u21_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1288 h u18_298 hv
  have u22_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1932 h u5_121 u19_115 u13_118 hv
  have u23_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u20_108
  have u24_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21269 h hv u23_12 u21_86
  have u25_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28975 h hv u23_12 u17_50
  exact c1787 h u22_120 u12_204 u24_260 u11_295 u25_315 u8_325 u7_329 u6_330

end BorsukNine.FiniteObstruction

end OAI

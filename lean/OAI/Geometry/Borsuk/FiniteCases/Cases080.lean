import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases018
import OAI.Geometry.Borsuk.FiniteCases.Cases035
import OAI.Geometry.Borsuk.FiniteCases.Cases040
import OAI.Geometry.Borsuk.FiniteCases.Cases055
import OAI.Geometry.Borsuk.FiniteCases.Cases063
import OAI.Geometry.Borsuk.FiniteCases.Cases079

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31244 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a3 a315 n22 n186 n134
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u4_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u5_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u6_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u7_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u8_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u9_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u10_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u11_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u13_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u12_40
  have u14_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u13_39
  have u15_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c581 h hv u13_39
  have u16_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u12_40
  have u17_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u16_38
  have u18_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u19_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u18_101
  have u20_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u19_71
  have u21_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1500 h a315 hv
  have u22_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4891 h hv u19_71 u21_100
  have u23_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u18_101
  have u24_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u23_50
  have u25_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u26_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u27_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u28_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u29_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c29035 h a315 a3 u23_50 hv
  have u30_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u14_23
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c29064 h a315 hv u13_39 u25_76
  have u32_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u24_12 hv u25_76
  have u33_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c56 h hv u26_4
  have u34_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26045 h hv u1_2 a3 u28_6
  have u35_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv u29_51
  have u36_262 : Q {2, 3, 4, 6} := by
    by_contra hv
    exact c31243 h h0 hv a3 a315 n22 n134
  have u37_65 : T {2, 3, 4} := by
    by_contra hv
    exact c969 h u36_262 hv
  have u38_67 : T {2, 3, 6} := by
    by_contra hv
    exact c997 h u36_262 hv
  have u39_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1297 h u36_262 hv
  have u40_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c21545 h u36_262 u28_6 hv
  have u41_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5611 h hv u37_65 u19_71 u32_72
  have u42_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13497 h hv u37_65 u19_71 u32_72
  have u43_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21337 h hv u37_65 u19_71 u32_72
  have u44_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20483 h hv u2_9 u37_65 u38_67
  have u45_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20623 h hv u2_9 u37_65 u38_67
  have u46_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20763 h hv u2_9 u37_65 u38_67
  have u47_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u8_121 hv u40_116
  have u48_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17762 h hv u30_10 u40_116
  have u49_295 : Q {2, 7, 8, 9} := by
    by_contra hv
    exact c1795 h a315 u42_204 u43_260 hv u4_325 u3_329 u5_330
  have u50_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18565 h hv u14_23 u32_72 u47_105
  have u51_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16465 h hv u14_23 u39_87 u47_105
  have u52_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1275 h u49_295 hv
  have u53_86 : T {3, 4, 5} := by
    by_contra hv
    exact c26168 h u49_295 u20_5 hv
  have u54_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c26259 h u49_295 hv u53_86 u39_87
  have u55_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c26175 h u49_295 hv u23_50
  have u56_17 : T {0, 3, 5} := by
    by_contra hv
    exact c26172 h u49_295 hv u29_51
  have u57_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17351 h hv u14_23 u52_85
  have u58_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13399 h hv u23_50 u19_71 u53_86
  have u59_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15662 h hv u54_16 u40_116
  have u60_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20878 h hv u30_10 u54_16 n22
  have u61_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21018 h hv u30_10 u54_16 n22
  have u62_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21158 h hv u30_10 u54_16 n22
  have u63_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19899 h hv u31_11 u56_17 u17_27
  have u64_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c882 h hv u22_143 u59_220 u48_235 u35_245 u60_257 u61_258
  have u65_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1772 h hv u58_203 u62_259 u34_294 u27_314 u7_324 u6_328 u5_330
  have u66_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c947 h hv u41_148 u51_225 u50_240 u63_250 u46_256 u62_259 u43_260
  have u67_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c835 h hv u33_140 u15_217 u57_232 u64_251 u44_254 u45_255
  have u68_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u8_121 hv u65_119
  have u69_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26450 h hv u24_12 u66_64
  have u70_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23650 h hv u55_18 u66_64
  exact c1517 h u68_102 n186 u67_242 u70_277 u69_297 u11_316 u10_319 u9_320

private theorem c31245 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {2, 3, 5, 7} → ¬ Q {0, 3, 8, 9} → ¬ T {6, 8, 9} →
      ¬ Q {2, 4, 8, 9} → T {0, 1, 7} → T {1, 4, 6} → T {2, 5, 6} → ¬ T {0, 2, 6} →
      T {2, 4, 5} → T {1, 2, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n116 n267 n184 n119 n285 a6 a51 a76 n12 a71 a40 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 a71
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 a76
  have u7_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u8_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv a51 u7_120
  have u9_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 a40 hv a76
  have u10_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv a40
  have u11_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u10_39
  have u12_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u10_39
  have u13_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv n116
  have u14_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u15_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1934 h u1_121 hv n116 n119
  have u16_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22475 h hv u11_23 a51 u14_105
  have u17_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22615 h hv u11_23 a51 u14_105
  have u18_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23465 h hv u11_23 a51 u14_105
  have u19_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22105 h hv a6 u15_110
  have u20_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 n184 hv u18_275 u6_305 u13_311 u5_314
  have u21_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c983 h hv u8_150 u12_206 u19_266 n267 u16_268 u17_269
  have u22_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c18481 h u20_240 hv a71
  have u23_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18540 h u20_240 n12 u9_72 hv
  have u24_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u8_150 u12_206 u21_261 u19_266 n267 u16_268 u17_269
  have u25_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19880 h hv u22_31 u24_66
  have u26_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12103 h hv a40 a76 u23_80
  exact c1637 h u15_110 u26_194 u25_250 n285 u6_305 u4_321 u3_324 u2_325

private theorem c31246 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {1, 3, 8, 9} → T {5, 8, 9} → ¬ Q {0, 3, 8, 9} →
      ¬ Q {3, 6, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ T {1, 5, 6} → T {1, 4, 6} →
      T {0, 2, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n311 n240 a116 n184 n314 n305 n55 a51 a10 a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u5_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u4_40
  have u6_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u5_39
  have u7_275 : Q {2, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 n184 n240 hv n305 n311 n314
  have u8_59 : T {1, 6, 7} := by
    by_contra hv
    exact c23370 h u7_275 n22 hv
  have u9_24 : T {0, 4, 7} := by
    by_contra hv
    exact c23374 h u7_275 hv n55
  have u10_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12911 h hv u4_40 a51 u8_59
  have u11_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20743 h hv a10 u6_23 u9_24
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1733 h hv u10_200 u11_256 n311 u3_321 u2_328 u1_329
  exact c1727 h a116 u10_200 u11_256 u12_291 n311 u3_321 u2_328 u1_329

theorem c31247 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {0, 1, 7} → ¬ T {0, 1, 4} → Q {3, 7, 8, 9} →
      ¬ T {0, 4, 5} → ¬ Q {0, 3, 4, 5} → False := by
  classical
  intro a102 a6 n3 a315 n22 n170
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u4_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u3_101
  have u5_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u4_71
  have u6_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 n3 hv u5_5
  have u7_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24785 h hv u0_2 u6_4 a6
  have u8_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 u4_71
  have u9_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 n3 hv
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 u9_76
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u13_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u1_1 hv u12_40
  have u14_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 n3 u13_38 hv
  have u15_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u14_51 u11_120
  have u16_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u12_40 hv u9_76
  have u17_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u13_38
  have u18_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u17_27 hv u9_76
  have u19_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 n3 hv n22
  have u20_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv n3
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u1_1 hv u12_40
  have u22_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u21_39
  have u23_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u4_71 u11_120
  have u24_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u3_101
  have u25_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u24_50
  have u26_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u24_50 u11_120
  have u27_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u2_121 a102 hv
  have u28_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u12_40 a102
  have u29_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10155 h hv u24_50 u4_71 a102
  have u30_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10295 h hv u24_50 u4_71 a102
  have u31_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22242 h hv n3 u27_119
  have u32_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8942 h hv u21_39 u27_119
  have u33_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31245 h h0 hv u31_267 u28_184 u27_119 u7_285 a6 u14_51 u9_76 u25_12 u4_71 u12_40 a315
  have u34_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u33_116
  have u35_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1937 h u2_121 hv u33_116 u11_120
  have u36_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6145 h hv u14_51 u33_116
  have u37_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18568 h hv u16_72 u3_101 u34_105
  have u38_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9924 h hv u21_39 u35_110
  have u39_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31246 h h0 hv u37_240 u33_116 u28_184 u8_314 u10_305 u18_55 u14_51 u19_10 a315 n22
  have u40_80 : T {2, 6, 7} := by
    by_contra hv
    exact c28404 h u39_311 n3 hv
  have u41_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28412 h u39_311 u25_12 hv
  have u42_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28417 h u39_311 u22_23 hv
  have u43_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9151 h hv u12_40 u9_76 u40_80
  have u44_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9291 h hv u12_40 u9_76 u40_80
  have u45_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6303 h hv u24_50 u14_51 u41_52
  have u46_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6443 h hv u24_50 u14_51 u41_52
  have u47_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9364 h hv u42_41 u35_110
  have u48_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c124 h u2_121 hv u15_150 u26_151 u36_152 u45_153 u46_154
  have u49_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c263 h hv u23_130 u26_151 u47_175 u38_179 u29_180 u30_181
  exact c231 h u48_149 u20_128 n170 u49_171 u32_172 u43_173 u44_174

end BorsukNine.FiniteObstruction

end OAI

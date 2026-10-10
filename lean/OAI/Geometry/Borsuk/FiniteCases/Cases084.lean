import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases039
import OAI.Geometry.Borsuk.FiniteCases.Cases083

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31269 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n185 n71 n120
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u6_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u7_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u8_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u9_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u7_101 u5_276
  have u10_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u9_241 hv
  have u11_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h u9_241 hv
  have u12_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u9_241 hv
  have u13_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u9_241 n185 u5_276 hv u2_316 u1_317 u0_318
  have u14_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u13_296 hv
  have u15_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u13_296 hv
  have u16_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u17_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u4_121 u16_102 hv
  have u18_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u14_86 u17_119
  have u19_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31268 h h0 hv n185 n71 n120
  have u20_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u19_311 hv
  have u21_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h u19_311 hv
  have u22_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1496 h u19_311 hv
  have u23_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h u19_311 hv
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c28403 h u19_311 u3_1 hv
  have u25_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28415 h u19_311 hv u11_51
  have u26_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6909 h hv u15_91 u20_93 u21_94
  have u27_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2673 h hv u14_86 u15_91 u20_93
  have u28_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2533 h hv u14_86 u15_91 u21_94
  have u29_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2255 h hv u14_86 u20_93 u21_94
  have u30_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1967 h hv u15_91 u20_93 u21_94
  have u31_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1935 h u4_121 hv u23_116 u17_119
  have u32_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1838 h u4_121 u16_102 u24_105 hv
  have u33_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1840 h u4_121 u16_102 u24_105 hv
  have u34_64 : T {1, 8, 9} := by
    by_contra hv
    exact c26310 h u13_296 u25_13 hv
  have u35_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c4 h u4_121 u30_122 hv u29_124 u18_125 u28_126 u27_127
  have u36_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u4_121 u31_110 hv
  have u37_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1817 h u4_121 u32_108 hv
  have u38_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1819 h u4_121 u33_109 hv
  have u39_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6835 h hv u34_64 u22_100 u23_116
  have u40_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5855 h hv u34_64 u23_116 u17_119
  have u41_4 : T {0, 1, 5} := by
    by_contra hv
    exact c48 h u35_123 hv
  have u42_39 : T {1, 2, 5} := by
    by_contra hv
    exact c573 h u35_123 hv
  have u43_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c2085 h u35_123 hv u17_119
  have u44_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7075 h hv u12_55 u15_91 u36_111
  have u45_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7215 h hv u12_55 u15_91 u36_111
  have u46_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23151 h hv u41_4 u10_50 u12_55
  have u47_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23291 h hv u41_4 u10_50 u12_55
  have u48_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28619 h hv u41_4 u42_39 u10_50
  have u49_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28759 h hv u41_4 u42_39 u10_50
  have u50_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10379 h hv u42_39 u10_50 u12_55
  have u51_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10519 h hv u42_39 u10_50 u12_55
  have u52_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27351 h hv u41_4 u42_39 u12_55
  have u53_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27491 h hv u41_4 u42_39 u12_55
  have u54_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c137 h hv u30_122 u40_149 u6_155 u39_156 u26_157 u44_158 u45_159
  have u55_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u54_10 u37_113
  have u56_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18322 h hv u54_10 u38_112
  have u57_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1467 h hv u50_182 u55_238 u46_273 u52_303 u48_312 u8_315
  have u58_98 : ¬ T {3, 7, 8} := by
    intro hv
    exact c1457 h hv u50_182 u55_238 u46_273 u52_303 u57_309 u48_312 u8_315
  have u59_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1482 h hv u51_183 u56_239 u47_274 u53_304 u49_313 u8_315
  have u60_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c1472 h hv u51_183 u56_239 u47_274 u53_304 u59_310 u49_313 u8_315
  exact c2122 h u35_123 u43_88 u58_98 u60_99

theorem c31274 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → T {6, 8, 9} → False := by
  classical
  intro n203 n294 n314 a119
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c1776 h hv n203 n294 n314 u2_324 u1_328 u0_330
  exact c1772 h a119 n203 u3_259 n294 n314 u2_324 u1_328 u0_330

theorem c31281 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → T {4, 6, 7} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro n280 n245 a105 n189
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1562 h a105 n189 n245 n280 hv u0_316 u1_322 u2_323
  exact c1570 h u3_300 n189 n245 n280 u0_316 u1_322 u2_323

theorem c31288 (h : TenSystem T Q) :
    ¬ Q {3, 5, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 6, 7, 9} → T {3, 7, 9} → ¬ Q {1, 3, 7, 9} → False := by
  classical
  intro n310 n183 n315 n274 n313 a99 n239
  have u0_304 : Q {3, 4, 7, 9} := by
    by_contra hv
    exact c1472 h a99 n183 n239 n274 hv n310 n313 n315
  exact c1480 h u0_304 n183 n239 n274 n310 n313 n315

theorem c31290 (h : TenSystem T Q) :
    ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → T {0, 2, 4} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 4, 5} → False := by
  classical
  intro n157 n158 n159 a10 n156 n122 n155
  have u0_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c137 h a10 n122 hv n155 n156 n157 n158 n159
  exact c141 h u0_149 n122 n155 n156 n157 n158 n159

theorem c31297 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → T {1, 5, 7} → Q {0, 2, 4, 9} → ¬ Q {3, 4, 6, 8} → ¬ T {6, 8, 9} → False := by
  classical
  intro n117 a149 n246 a56 a159 n301 n119
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
  have u4_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1906 h u0_121 hv n117 n119
  have u5_45 : T {1, 3, 5} := by
    by_contra hv
    exact c7122 h a159 hv n117
  have u6_58 : T {1, 5, 9} := by
    by_contra hv
    exact c5728 h a149 hv n117
  have u7_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11505 h hv u5_45 a56 u6_58
  have u8_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24277 h hv u5_45 a56 u6_58
  exact c1577 h u4_106 u7_190 n246 u8_281 n301 u3_317 u2_322 u1_324

private theorem c31298 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {6, 7, 8} → Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → T {1, 5, 7} → Q {0, 2, 4, 9} → ¬ Q {3, 4, 6, 8} → False := by
  classical
  intro a106 a117 a149 n246 a56 a159 n301
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
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1903 h u0_121 a106 hv a117
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c7126 h a159 hv u4_112
  have u6_63 : T {1, 7, 9} := by
    by_contra hv
    exact c5738 h a149 hv u4_112
  have u7_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11513 h hv u5_47 a56 u6_63
  have u8_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24285 h hv u5_47 a56 u6_63
  exact c1577 h a106 u7_190 n246 u8_281 n301 u3_317 u2_322 u1_324

private theorem c31299 (h : TenSystem T Q) :
    ¬ Q {1, 2, 5, 7} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 5, 6, 7} → T {1, 5, 7} → ¬ Q {0, 1, 5, 7} → False := by
  classical
  intro n217 n255 n254 n232 n251 a56 n140
  have u0_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c827 h a56 n140 n217 n232 hv n251 n254 n255
  exact c835 h u0_242 n140 n217 n232 n251 n254 n255

private theorem c31300 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  classical
  intro a149 n246 a159 n96 n119
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u2_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u3_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u0_9 u1_10 u2_15
  have u4_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u0_9 u1_10 u2_15
  have u5_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u6_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u7_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31297 h h0 hv a149 n246 u5_56 a159 u6_301 n119
  have u8_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c7123 h a159 hv u7_117
  have u9_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c5729 h a149 hv u7_117
  have u10_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c671 h hv u8_45
  have u11_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c868 h hv u9_58
  have u12_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31298 h h0 hv u7_117 a149 n246 u5_56 a159 u6_301
  have u13_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15364 h hv n96 u12_106 n119
  have u14_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4584 h hv n96 u12_106 n119
  exact c31299 h u13_217 u11_255 u3_254 u10_232 u4_251 u5_56 u14_140

theorem c31301 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → Q {0, 2, 4, 9} → False := by
  classical
  intro a232 a159
  have u0_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u1_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u2_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u3_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u4_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c17357 h a232 hv u0_75
  have u5_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17365 h a232 u3_10 hv u2_15
  have u6_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c17373 h a232 u3_10 hv u1_26
  exact c17378 h a232 u5_12 u6_23 u4_32

theorem c31302 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n140 n217 a159 n96
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u3_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u4_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u5_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u0_9 u3_10 u4_15
  have u6_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u0_9 u3_10 u4_15
  have u7_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u8_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c31299 h n217 hv u5_254 u2_232 u6_251 u7_56 n140
  have u9_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c841 h u8_255 n140 n217 u2_232 hv u6_251 u5_254
  have u10_63 : T {1, 7, 9} := by
    by_contra hv
    exact c941 h u8_255 hv
  have u11_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1715 h u8_255 hv
  have u12_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h u8_255 u0_9 hv
  have u13_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u9_242 hv
  have u14_52 : T {1, 4, 7} := by
    by_contra hv
    exact c774 h u9_242 hv
  have u15_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u9_242 u0_9 hv
  have u16_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6329 h hv u14_52 u7_56 u10_63
  have u17_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6041 h hv u14_52 u7_56 u10_63
  have u18_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19303 h hv u0_9 u11_115
  have u19_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1904 h u1_121 u12_106 hv u15_119
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1906 h u1_121 u12_106 hv u15_119
  have u21_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6423 h hv u13_50 u20_117
  have u22_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c31300 h h0 hv u18_246 a159 n96 u15_119
  have u23_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u1_121 hv u19_112
  have u24_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c7251 h a159 hv u19_112 u20_117
  have u25_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5872 h hv u24_60 u23_109
  have u26_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6260 h hv u24_60 u12_106 u15_119
  exact c124 h u1_121 u22_149 u25_150 u17_151 u26_152 u16_153 u21_154

end BorsukNine.FiniteObstruction

end OAI

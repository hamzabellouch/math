import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases090

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31485 (h : TenSystem T Q) :
    ¬ Q {0, 3, 5, 9} → T {0, 3, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → False := by
  classical
  intro n178 a21 n183 n184 n133 n154 n174
  have u0_181 : Q {0, 3, 6, 9} := by
    by_contra hv
    exact c302 h a21 n133 n154 n174 n178 hv n183 n184
  exact c312 h u0_181 n133 n154 n174 n178 n183 n184

theorem c31487 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → T {0, 4, 6} → ¬ Q {0, 4, 6, 9} → False := by
  classical
  intro n171 n185 n189 n135 n156 a23 n191
  have u0_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c332 h a23 n135 n156 n171 n185 n189 hv n191
  exact c344 h u0_190 n135 n156 n171 n185 n189 n191

theorem c31500 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → T {6, 7, 9} → ¬ Q {0, 6, 7, 9} → False := by
  classical
  intro n258 n313 a118 n202
  have u0_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u3_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1757 h a118 n202 n258 hv n313 u0_323 u1_327 u2_330
  exact c1763 h u3_293 n202 n258 n313 u0_323 u1_327 u2_330

private theorem c31503 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → T {2, 4, 5} → Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n29 a71 a258 a313 a304
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u2_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5031 h hv a71 u1_99
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u4_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u5_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10081 h hv u4_63 a71
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8095 h hv u4_63 u1_99 u6_109
  have u8_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u0_37 u6_109
  have u9_38 : T {1, 2, 4} := by
    by_contra hv
    exact c28700 h a313 n29 hv
  have u10_65 : T {2, 3, 4} := by
    by_contra hv
    exact c21000 h a258 n29 hv
  have u11_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27478 h a304 u3_7 n29 hv
  have u12_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13351 h hv u9_38 u10_65 a71
  have u13_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13071 h hv u9_38 u10_65 a71
  have u14_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c31309 h u8_196 u12_203 u7_165 u13_201 hv u5_180 u11_32
  exact c475 h u14_190 u2_144 u7_165 u5_180 u8_196 u13_201 u12_203

private theorem c31504 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 4, 5} → ¬ Q {0, 2, 4, 8} → Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {1, 2, 5, 8} → ¬ Q {0, 1, 2, 5} → Q {3, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro a71 n158 a258 a313 n105 n107 n260 n218 n123 a304 n255 n239 n187
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u2_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c20995 h a258 hv a71
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u4_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c292 h hv u2_20
  have u5_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15528 h hv u2_20 n105
  have u6_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15246 h hv u2_20 n107
  have u7_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c97 h hv u3_7
  have u8_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u3_7 hv
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31503 h h0 hv a71 a258 a313 a304
  have u10_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u9_29 hv
  have u11_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u9_29 hv
  have u12_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c21001 h a258 u9_29 hv
  have u13_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u10_38
  have u14_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c594 h hv u11_40
  have u15_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5442 h hv u12_65 u1_112
  have u16_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c576 h hv n123 u13_211 u14_216 u6_217 n218 u5_219
  have u17_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c572 h hv n123 u16_206 u13_211 u14_216 u6_217 n218 u5_219
  have u18_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28698 h a313 hv u17_39
  have u19_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u17_39
  have u20_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16281 h hv u18_25 u9_29 u19_32
  have u21_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c21039 h a258 hv u18_25 u9_29
  have u22_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c944 h a258 u15_147 u20_224 n239 hv n255 n260
  have u23_55 : T {1, 5, 6} := by
    by_contra hv
    exact c27434 h a304 u21_14 hv
  have u24_91 : T {3, 5, 6} := by
    by_contra hv
    exact c19728 h u22_249 u21_14 hv
  have u25_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11859 h hv u23_55 u8_76 u24_91
  have u26_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12139 h hv u23_55 u8_76 u24_91
  exact c31431 h u4_173 u7_137 n187 u26_194 u25_192 u18_25 n158

theorem c31505 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 3, 7, 9} → T {6, 7, 9} → False := by
  classical
  intro a258 a313 a304 n255 n239 a118
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1425 h a313 hv
  have u5_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u2_121 hv a118
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u3_1 hv
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u2_121 u5_103 u6_112 hv
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u7_116
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u2_121 u5_103 u6_112 hv
  have u10_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u2_121 hv u9_114
  have u11_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u12_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u2_121 u11_109 a118 hv
  have u13_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u12_120
  have u14_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25043 h hv u1_2 u11_109
  have u15_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u16_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15521 h hv u15_99 u11_109 a118
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2207 h hv u15_99 u11_109 a118
  have u18_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11043 h hv u0_37 a118
  have u19_59 : T {1, 6, 7} := by
    by_contra hv
    exact c885 h a258 hv
  have u20_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u21_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7101 h hv u19_59 u4_95 a118
  have u22_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8095 h hv u20_63 u15_99 u11_109
  have u23_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c31504 h h0 hv u21_158 a258 a313 u8_105 u10_107 u13_260 u16_218 u17_123 a304 n255 n239 u18_187
  have u24_7 : T {0, 1, 8} := by
    by_contra hv
    exact c28688 h a313 hv u23_71
  have u25_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28804 h a313 hv u23_71 u5_103
  have u26_22 : T {0, 4, 5} := by
    by_contra hv
    exact c21100 h a258 hv u23_71 u5_103
  have u27_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21104 h a258 u23_71 hv u5_103
  have u28_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28707 h a313 u3_1 hv u24_7
  have u29_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15811 h hv u26_22 u15_99
  have u30_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22811 h hv u26_22 u20_63
  have u31_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26139 h hv u26_22 u25_50 u27_86
  have u32_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25859 h hv u26_22 u25_50 u27_86
  have u33_81 : T {2, 6, 8} := by
    by_contra hv
    exact c27424 h a304 u28_4 hv
  have u34_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c1210 h hv u22_165 u29_221 u30_271 u14_287 u32_292 u31_294
  exact c1202 h u33_81 u22_165 u29_221 u30_271 u34_281 u14_287 u32_292 u31_294

theorem c31506 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 4, 5} → ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n71 n258 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u4_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u2_109 hv u3_118
  have u5_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1812 h u0_121 hv u4_115
  have u6_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u4_115
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u2_109 u3_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u7_120
  have u9_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u7_120
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u1_1 hv
  have u11_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u12_7 : T {0, 1, 8} := by
    by_contra hv
    exact c28688 h a313 hv n71
  have u13_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28804 h a313 hv n71 u10_103
  have u14_22 : T {0, 4, 5} := by
    by_contra hv
    exact c28802 h a313 hv n71 u10_103
  have u15_185 : Q {0, 4, 5, 6} := by
    by_contra hv
    exact c31269 h h0 hv n71 u7_120
  have u16_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u11_276 u8_101
  have u17_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27447 h a304 u1_1 hv u12_7
  have u18_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28707 h a313 u1_1 hv u12_7
  have u19_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28705 h a313 u1_1 hv u12_7
  have u20_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv u13_50 u3_118
  have u21_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23175 h hv u14_22 u13_50 u8_101
  have u22_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14123 h hv u14_22 u3_118
  have u23_23 : T {0, 4, 6} := by
    by_contra hv
    exact c339 h u15_185 hv
  have u24_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21824 h hv u17_5 u4_115
  have u25_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27426 h a304 u17_5 hv
  have u26_81 : T {2, 6, 8} := by
    by_contra hv
    exact c27424 h a304 u18_4 hv
  have u27_74 : T {2, 4, 8} := by
    by_contra hv
    exact c28686 h a313 u18_4 hv
  have u28_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22802 h hv u19_3 u4_115
  have u29_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18427 h hv u23_23 u8_101 u5_106
  have u30_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16327 h hv u23_23 u8_101 u5_106
  have u31_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c1030 h hv u20_153 u22_209 u24_264 u28_271 u21_273 u16_275
  have u32_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5501 h hv u27_74 u25_78 u26_81
  have u33_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c1022 h hv u20_153 u22_209 u24_264 u31_268 u28_271 u21_273 u16_275
  have u34_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c940 h hv u32_147 u30_224 u29_239 u6_255 n258 u9_260
  have u35_63 : T {1, 7, 9} := by
    by_contra hv
    exact c10778 h u15_185 hv u33_69
  exact c932 h u35_63 u32_147 u30_224 u29_239 u34_249 u6_255 n258 u9_260

theorem c31507 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 5} → T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a22 a63 a71 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5987 h hv a63 u2_109 u1_118
  have u4_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6417 h hv a63 u2_109 u1_118
  have u5_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u6_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u2_109 u1_118 hv
  have u7_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 a22 hv
  have u8_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28799 h a313 a22 hv a71
  have u9_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u5_7 u7_42 hv
  have u10_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u5_7 u7_42 hv
  have u11_60 : T {1, 6, 8} := by
    by_contra hv
    exact c27508 h a304 u5_7 u7_42 hv
  have u12_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6002 h hv u8_50 u6_120
  have u13_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5727 h hv u10_57 u1_118
  have u14_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6187 h hv u9_53 u10_57 u11_60
  have u15_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6475 h hv u9_53 u10_57 u11_60
  exact c124 h u0_121 u13_149 u3_150 u12_151 u14_152 u4_153 u15_154

end BorsukNine.FiniteObstruction

end OAI

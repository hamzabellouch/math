import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases007
import OAI.Geometry.Borsuk.FiniteCases.Cases014
import OAI.Geometry.Borsuk.FiniteCases.Cases015
import OAI.Geometry.Borsuk.FiniteCases.Cases016
import OAI.Geometry.Borsuk.FiniteCases.Cases027
import OAI.Geometry.Borsuk.FiniteCases.Cases030
import OAI.Geometry.Borsuk.FiniteCases.Cases048
import OAI.Geometry.Borsuk.FiniteCases.Cases050
import OAI.Geometry.Borsuk.FiniteCases.Cases054
import OAI.Geometry.Borsuk.FiniteCases.Cases065
import OAI.Geometry.Borsuk.FiniteCases.Cases067
import OAI.Geometry.Borsuk.FiniteCases.Cases069
import OAI.Geometry.Borsuk.FiniteCases.Cases071
import OAI.Geometry.Borsuk.FiniteCases.Cases078

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31236 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 6} → T {4, 5, 7} → T {0, 2, 5} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {0, 1, 6} → ¬ T {1, 2, 5} → T {0, 5, 6} → T {0, 1, 4} → T {0, 4, 6} → T {2, 4, 5} → T {1, 4, 5} → T {1, 2, 6} → ¬ T {4, 5, 6} → ¬ T {1, 2, 4} → ¬ T {0, 4, 5} → False := by
  classical
  intro a209 n207 a102 a11 n307 n311 n12 n5 n39 a27 a3 a23 a71 a50 a40 n101 n38 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10155 h hv a50 a71 a102
  have u2_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv a40 a102
  have u3_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c63 h hv n5
  have u4_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c579 h hv n39
  have u5_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv n38
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c14122 h a209 n22 hv
  have u7_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c14125 h a209 a23 hv
  have u8_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c14131 h a209 a27 hv
  have u9_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c14139 h a209 hv a102
  have u10_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14159 h a209 a23 a27 hv
  have u11_104 : T {4, 5, 9} := by
    by_contra hv
    exact c14184 h a209 n22 n101 hv
  have u12_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u0_1 u6_118
  have u13_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22383 h hv a3 u6_118
  have u14_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u6_118
  have u15_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv a50 u6_118
  have u16_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16923 h hv a11 u6_118
  have u17_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21824 h hv n5 u7_115
  have u18_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17484 h hv n12 u8_109
  have u19_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27300 h hv u9_33 n39
  have u20_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28140 h hv u9_33 n38
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27580 h hv u10_31 n39
  have u22_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10347 h hv a40 u11_104
  have u23_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c1384 h hv u18_233 u13_268 u12_298 n307 u20_309 n311
  have u24_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c293 h hv u14_132 u15_153 u23_177 u1_180 u22_182 u2_184
  have u25_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c287 h hv u14_132 u15_153 u24_173 u23_177 u1_180 u22_182 u2_184
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u24_173 u16_229 u17_264 u12_298 u19_303 u21_305
  have u27_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u23_177 u18_233 u13_268 u12_298 n307 u20_309 n311
  have u28_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c1322 h hv u24_173 u16_229 u17_264 u12_298 u26_301 u19_303 u21_305
  have u29_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15738 h hv u25_20 u28_89 u27_93
  have u30_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16026 h hv u25_20 u28_89 u27_93
  have u31_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c599 h hv u3_124 n207 u5_212 u4_216 u29_220 u30_222
  exact c587 h a40 u3_124 n207 u5_212 u4_216 u29_220 u31_221 u30_222

private theorem c31237 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → T {4, 5, 7} → ¬ Q {3, 5, 6, 8} → ¬ T {0, 2, 6} → ¬ T {0, 1, 6} → ¬ Q {2, 5, 6, 8} → T {2, 4, 6} → T {0, 5, 6} → T {0, 1, 7} → T {0, 4, 6} → T {1, 4, 5} → ¬ T {4, 5, 6} → T {7, 8, 9} → T {3, 7, 9} → ¬ T {1, 2, 4} → ¬ T {0, 4, 5} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a210 n262 n263 a102 n307 n12 n5 n287 a72 a27 a6 a23 a50 n101 a120 a99 n38 n22 n149 n134
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4611 h hv a72 a99
  have u6_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15391 h hv a23 a99
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u0_9 a120
  have u8_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv n38
  have u9_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv n38
  have u10_49 : T {1, 3, 9} := by
    by_contra hv
    exact c725 h a210 hv
  have u11_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h a210 hv
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c14262 h a210 n22 hv
  have u13_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c14265 h a210 a23 hv
  have u14_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c14271 h a210 a27 hv
  have u15_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c14279 h a210 hv a102
  have u16_34 : T {0, 7, 8} := by
    by_contra hv
    exact c14280 h a210 hv n101
  have u17_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14299 h a210 a23 a27 hv
  have u18_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12413 h hv u10_49 u11_70 a99
  have u19_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20437 h hv a23 u11_70
  have u20_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19023 h hv u0_9 u12_117
  have u21_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u13_114
  have u22_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21964 h hv n5 u13_114
  have u23_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u1_121 u14_108 hv
  have u24_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16530 h hv n12 u17_31 u15_32
  have u25_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21523 h hv u16_34 u12_117 a120
  have u26_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1671 h hv u18_196 n287 n307 u4_317 u3_326 u2_328
  have u27_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31230 h u24_226 u20_244 n134 u8_211 u7_241 hv a50
  have u28_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17577 h hv a23 a72 u21_107
  have u29_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21827 h hv a6 u23_113
  have u30_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv n149 u9_205 u25_261 n262 n263 u29_264 u22_265
  have u31_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c747 h u27_242 n134 u8_211 u24_226 u7_241 hv u20_244
  have u32_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20720 h hv u17_31 u30_65
  exact c850 h u31_243 u5_141 u6_218 u28_233 u26_252 u19_254 u32_256

private theorem c31238 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 5} → ¬ Q {0, 2, 3, 6} → ¬ T {1, 4, 6} → T {0, 1, 4} → T {1, 4, 5} → ¬ T {0, 4, 5} → ¬ Q {0, 2, 3, 4} → False := by
  classical
  intro a270 n4 n151 n51 a3 a50 n22 n149
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c22663 h a270 a3 hv
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c22664 h a270 n4 hv
  have u3_64 : T {1, 8, 9} := by
    by_contra hv
    exact c22670 h a270 n22 hv
  have u4_53 : ¬ T {1, 4, 8} := by
    intro hv
    exact c22723 h a270 a3 a50 hv
  have u5_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c22725 h a270 a3 a50 hv
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv u1_116
  have u7_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6144 h hv n51 u1_116
  have u8_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 u2_110 hv
  have u9_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5881 h hv u3_64 u6_105
  have u10_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6428 h hv u4_53 u8_111
  have u11_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6288 h hv u5_54 u8_111
  exact c124 h u0_121 n149 u9_150 n151 u7_152 u11_153 u10_154

private theorem c31239 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → ¬ T {0, 1, 5} → T {0, 1, 7} → ¬ T {0, 4, 5} → False := by
  classical
  intro a271 a24 n4 a6 n22
  have u0_28 : T {0, 5, 7} := by
    by_contra hv
    exact c22838 h a271 n4 n22 hv
  exact c22847 h a271 a6 a24 u0_28

private theorem c31240 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 6, 7} → T {2, 4, 6} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {0, 1, 5} → ¬ Q {0, 2, 3, 6} → ¬ Q {2, 3, 5, 6} → T {0, 1, 7} → T {1, 2, 6} → ¬ T {0, 4, 5} → False := by
  classical
  intro a207 n262 n270 a72 n291 n311 n4 n151 n266 a6 a40 n22
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u3_67 : T {2, 3, 6} := by
    by_contra hv
    exact c995 h a207 hv
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12939 h hv a40 u3_67 a72
  have u5_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1731 h hv u4_200 n291 n311 u2_321 u1_328 u0_329
  have u6_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1727 h hv u4_200 u5_256 n291 n311 u2_321 u1_328 u0_329
  have u7_24 : T {0, 4, 7} := by
    by_contra hv
    exact c13844 h a207 hv u6_116
  have u8_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c31239 h hv u7_24 n4 a6 n22
  have u9_272 : Q {2, 3, 6, 9} := by
    by_contra hv
    exact c996 h a207 n151 n262 n266 n270 u8_271 hv
  have u10_28 : T {0, 5, 7} := by
    by_contra hv
    exact c22978 h u9_272 n4 n22 hv
  exact c22987 h u9_272 a6 u7_24 u10_28

private theorem c31242 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → ¬ Q {2, 3, 4, 6} → T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a102 n262 a3 a315 n22 n134
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u4_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u5_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u6_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22103 h hv a3 u5_120
  have u7_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u7_101
  have u9_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u8_50 u5_120
  have u10_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u1_1 a3 hv
  have u11_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28425 h hv u1_1 a3 u4_6
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25625 h hv u0_2 a3 u4_6
  have u13_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u8_50
  have u14_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u15_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u13_12 hv u14_76
  have u16_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c29035 h a315 a3 u8_50 hv
  have u17_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u1_1 hv u3_40
  have u18_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u17_39
  have u19_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u18_23
  have u20_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u19_10
  have u21_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c31238 h h0 hv u10_4 u9_151 u16_51 a3 u8_50 n22 u20_149
  have u22_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c31240 h h0 hv n262 u21_270 u15_72 u12_291 u11_311 u10_4 u9_151 u6_266 u4_6 u3_40 n22
  have u23_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27863 h hv u1_1 a3 u4_6
  have u24_11 : T {0, 2, 5} := by
    by_contra hv
    exact c29064 h a315 hv u17_39 u14_76
  have u25_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1485 h a315 hv
  have u26_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25045 h hv a3 u25_99
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u17_39
  have u28_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u1_1 hv u3_40
  have u29_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u28_38
  have u30_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u28_38
  have u31_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u7_101
  have u32_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u31_71
  have u33_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u2_121 a102 hv
  have u34_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c31236 h h0 hv u22_207 a102 u24_11 u23_307 u11_311 u13_12 u32_5 u17_39 u29_27 a3 u18_23 u31_71 u8_50 u3_40 u7_101 u28_38 n22
  have u35_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u10_4 u33_119
  have u36_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u33_119
  have u37_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c544 h u2_121 u30_205 u27_206 u22_207 u36_208 u34_209 hv
  exact c31237 h h0 u37_210 n262 u35_263 a102 u23_307 u13_12 u32_5 u26_287 u15_72 u29_27 u4_6 u18_23 u8_50 u7_101 u5_120 u25_99 u28_38 n22 u20_149 n134

theorem c31243 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 3, 4, 6} → T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro n262 a3 a315 n22 n134
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u3_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u2_40
  have u4_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u3_39
  have u5_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u4_23
  have u6_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u5_10
  have u7_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u8_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28425 h hv u0_1 a3 u7_6
  have u9_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u10_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u9_4
  have u11_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u12_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u11_101
  have u13_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u12_50
  have u14_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u15_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u13_12 hv u14_76
  have u16_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u14_76 u11_101
  have u17_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u18_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u2_40
  have u19_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u18_38
  have u20_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u18_38
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u11_101
  have u22_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u21_71
  have u23_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31242 h h0 hv n262 a3 a315 n22 n134
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u24_102 hv
  have u26_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1822 h u1_121 u11_101 u24_102 hv
  have u27_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1824 h u1_121 u11_101 u24_102 hv
  have u28_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23366 h hv u22_5 u24_102
  have u29_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u11_101 u24_102
  have u30_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u1_121 hv u25_119 u23_120
  have u31_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u1_121 hv u25_119 u23_120
  have u32_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21405 h hv u7_6 u25_119
  have u33_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u1_121 u26_103 hv
  have u34_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u1_121 u27_104 hv
  have u35_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1644 h hv u30_110
  have u36_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv u31_116
  have u37_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv u31_116
  have u38_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21684 h hv u22_5 u31_116
  have u39_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21822 h hv u9_4 u33_118
  have u40_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21962 h hv u9_4 u34_117
  have u41_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17622 h hv u5_10 u34_117
  have u42_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv u29_240 u28_275 u35_305 u8_311 u17_314
  have u43_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u6_149 u20_205 u32_261 n262 u38_263 u39_264 u40_265
  exact c31231 h h0 u42_184 u41_234 u25_119 u43_65 u37_105 u36_256 u19_211 u5_10 u15_72 u10_142 n134 u16_55 u11_101 u23_120

end BorsukNine.FiniteObstruction

end OAI

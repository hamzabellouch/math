import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases101

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31526 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n311 n29 n49 a304
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
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u6_57 : T {1, 5, 8} := by
    by_contra hv
    exact c27548 h a304 n29 hv u5_112
  have u7_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u6_57
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u9_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31525 h h0 hv n29 n49 a304
  have u10_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u4_121 hv u9_116
  have u11_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u4_121 u10_105 hv u8_118
  have u12_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u4_121 hv u11_117
  have u13_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18186 h hv u7_12 u12_104
  have u14_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u4_121 u10_105 hv u8_118
  have u15_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1821 h u4_121 hv u14_111
  have u16_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17344 h hv u7_12 u15_110
  have u17_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u0_1 u11_117
  have u18_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u0_1 u14_111
  have u19_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u4_121 hv u8_118
  have u20_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u4_121 u19_103 hv u9_116
  have u21_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u5_112 u20_114
  have u22_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27550 h a304 n29 hv u5_112
  have u23_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u6_57 u22_78 u9_116
  have u24_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17885 h hv u22_78 u19_103 u9_116
  have u25_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3305 h hv u22_78 u19_103 u9_116
  have u26_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u27_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv u26_40 u9_116
  have u28_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26863 h hv u0_1 u9_116
  have u29_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c27483 h a304 u0_1 hv u26_40
  have u30_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9082 h hv u29_39 u8_118
  have u31_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u29_39
  have u32_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c27487 h a304 u0_1 u26_40 hv
  have u33_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8666 h hv u32_42 u8_118
  have u34_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c620 h hv u32_42
  have u35_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27427 h a304 hv u22_78
  have u36_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27468 h a304 u35_5 u7_12 hv
  have u37_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u8_118
  have u38_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u39_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u40_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u41_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31521 h h0 hv a304
  have u42_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u9_116 u38_200 n311 hv
  have u43_79 : T {2, 5, 9} := by
    by_contra hv
    exact c1185 h u42_291 hv
  have u44_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1271 h u42_291 hv
  have u45_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c1733 h u42_291 u38_200 hv n311 u3_321 u2_328 u1_329
  have u46_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2789 h hv u43_79 u11_117
  have u47_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16797 h hv u36_32 u43_79
  have u48_58 : T {1, 5, 9} := by
    by_contra hv
    exact c870 h u45_256 hv
  have u49_64 : T {1, 8, 9} := by
    by_contra hv
    exact c956 h u45_256 hv
  have u50_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c696 h hv u25_131 u47_228 u16_232 u24_235 u13_238 u41_239
  have u51_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5729 h hv u48_58 u11_117
  have u52_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c544 h u4_121 u37_205 u31_206 hv u50_208 u34_209 u40_210
  have u53_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c241 h hv u46_128 u51_149 u33_170 u23_171 u27_172 u30_173
  have u54_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c13859 h u52_207 hv u19_103
  have u55_28 : T {0, 5, 7} := by
    by_contra hv
    exact c13850 h u52_207 hv u15_110
  have u56_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u53_174 u39_230 u21_265 u17_299 hv u18_305
  have u57_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27020 h hv u54_35 u29_39
  have u58_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26318 h hv u54_35 u32_42
  have u59_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21551 h hv u55_28 u49_64
  have u60_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16651 h hv u55_28 u44_85
  exact c1306 h u56_302 u23_171 u60_227 u59_262 u58_296 u28_300 u57_301

theorem c31527 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n29 n49 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u3_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u4_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv u3_118
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u1_1 hv
  have u6_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31525 h h0 hv n29 n49 a304
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u0_121 hv u7_116
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u0_121 u4_103 hv u7_116
  have u10_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u0_121 u8_105 hv u3_118
  have u11_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u0_121 u8_105 hv u3_118
  have u12_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u5_112 u9_114
  have u13_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u1_1 u10_111
  have u14_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u1_1 u11_117
  have u15_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31526 h h0 hv n29 n49 a304
  have u16_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28467 h u15_311 u1_1 u6_40 hv
  have u17_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9226 h hv u16_41 u5_112
  have u18_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27158 h hv n29 u16_41
  exact c1349 h a304 u17_174 u2_230 u12_265 u14_299 u18_302 u13_305

theorem c31528 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 6, 7} → ¬ Q {3, 4, 5, 8} → ¬ T {3, 6, 7} → ¬ T {1, 3, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n31 n298 n95 n49 n118
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
  have u4_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv n118
  have u5_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23796 h hv n31 n49
  have u6_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c19002 h hv n31 n95 n118
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1534 h hv u6_243 u5_278 n298 u3_317 u2_319 u1_321
  exact c31421 h h0 u6_243 u4_103 u7_187 u5_278

theorem c31529 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a311 a116 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u3_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u4_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u5_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u1_121 u4_105 hv u3_118
  have u6_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u2_90 u5_117
  have u7_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u0_1 u5_117
  have u8_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u1_121 u4_105 hv u3_118
  have u9_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u2_90 u8_111
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u0_1 u8_111
  have u11_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u12_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u11_29 hv
  have u13_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u3_118
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u1_121 u13_103 hv a116
  have u15_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u12_40 u14_114
  have u16_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u14_114
  have u17_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u18_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u19_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u18_99 u13_103
  have u20_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u21_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u22_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2373 h hv u20_93 u16_107
  have u23_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1949 h hv u21_94 u5_117
  have u24_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c4 h u1_121 u23_122 u6_123 u19_124 u22_125 u9_126 hv
  have u25_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h u24_127 hv u5_117
  have u26_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c2763 h u24_127 hv u8_111 u5_117
  have u27_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u25_86
  have u28_31 : T {0, 6, 7} := by
    by_contra hv
    exact c31528 h h0 hv u27_298 u26_95 n49 u3_118
  have u29_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22083 h hv u28_31 u8_111 u5_117
  have u30_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28421 h a311 u28_31 hv
  have u31_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u15_174 u17_230 u29_265 u7_299 hv u10_305
  have u32_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28468 h a311 u30_38 u12_40 hv
  exact c27159 h u31_302 u11_29 u32_41

theorem c31530 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ T {3, 6, 7} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 2, 5, 8} → T {0, 5, 8} → Q {3, 4, 7, 9} → False := by
  classical
  intro n38 n95 n141 n198 n162 a29 a304
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u0_37 u2_109
  have u4_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9642 h hv n38 u1_118
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12864 h hv n38 n95
  exact c31443 h u4_177 n141 a29 u5_200 n162 n198 u3_196

theorem c31531 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 2, 9} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a127 a116 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u5_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u6_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u5_118
  have u7_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u1_121 u6_103 hv a116
  have u8_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u7_114
  have u9_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u4_90 u8_107 u3_109
  have u10_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u7_114
  have u11_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u12_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u11_105
  have u13_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u1_121 u11_105 hv u5_118
  have u14_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u1_121 u11_105 hv u5_118
  have u15_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11323 h hv u2_37 a116
  have u16_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u17_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c1758 h hv u5_118
  have u18_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u19_43 : T {1, 2, 9} := by
    by_contra hv
    exact c633 h a127 hv
  have u20_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h a127 hv u13_117
  have u21_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c2763 h a127 hv u14_111 u13_117
  have u22_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2754 h a127 hv u18_112 u7_114
  have u23_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9929 h hv u19_43 u6_103
  have u24_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u20_86
  have u25_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7945 h hv u22_93 u6_103 a116
  have u26_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5005 h hv u22_93 u6_103 a116
  have u27_31 : T {0, 6, 7} := by
    by_contra hv
    exact c31528 h h0 hv u24_298 u21_95 n49 u5_118
  have u28_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31530 h h0 hv u21_95 u9_141 u10_198 u12_162 u16_29 a304
  have u29_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12185 h hv u2_37 u28_38 u19_43
  have u30_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13025 h hv u2_37 u28_38 u19_43
  exact c452 h u27_31 u26_143 u25_164 u23_179 u15_189 u29_195 u30_201 u17_202

end BorsukNine.FiniteObstruction

end OAI

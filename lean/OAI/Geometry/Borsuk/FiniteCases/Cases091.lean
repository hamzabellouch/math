import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases090

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31437 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → T {1, 3, 9} → False := by
  classical
  intro n230 n240 n210 a49
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u3_237 : Q {1, 3, 6, 9} := by
    by_contra hv
    exact c31423 h h0 hv n230 n210 n240 a49
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h u3_237 hv
  have u5_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23705 h hv u2_2 u4_46 a49
  have u6_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u4_46 a49
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11073 h hv u1_37 u4_46 a49
  have u8_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23845 h hv u2_2 u4_46 a49
  have u9_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12615 h hv u1_37 u4_46 a49
  have u10_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11775 h hv u1_37 u4_46 a49
  have u11_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31427 h h0 hv u3_237 a49
  have u12_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c31434 h h0 hv u10_192 u9_198 u8_278 u7_187 u6_186 u5_277 u3_237
  have u13_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c732 h u3_237 u12_133 n210 n230 hv u11_239 n240
  have u14_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h u13_234 hv
  have u15_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12051 h hv u1_37 u14_45 u4_46
  have u16_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31436 h h0 hv u13_234 u8_278 u7_187 u3_237
  have u17_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h u3_237 hv u16_103
  have u18_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c31435 h h0 u16_103 hv u13_234 u3_237
  have u19_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c17627 h u13_234 u17_13 hv
  have u20_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18054 h u3_237 hv u18_77
  have u21_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1846 h u0_121 u16_103 u19_106 hv
  have u22_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u16_103 u19_106 hv
  have u23_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c18153 h u3_237 u20_25 hv u21_108
  have u24_28 : T {0, 5, 7} := by
    by_contra hv
    exact c18056 h u3_237 hv u23_74
  have u25_31 : T {0, 6, 7} := by
    by_contra hv
    exact c17636 h u13_234 hv u23_74
  have u26_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27621 h hv u17_13 u24_28 u25_31
  have u27_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19919 h hv u17_13 u24_28 u25_31
  exact c31402 h h0 u27_250 u22_110 u26_305 u15_194

private theorem c31438 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 7} → Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → False := by
  classical
  intro n103 n167 n162 n161 a237 a230
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12891 h hv u1_37 u3_44 u4_46
  have u6_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25663 h hv u0_2 u3_44 u4_46
  have u7_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u8_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u2_121 n103 hv
  have u12_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u13_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7109 h hv u8_61 u7_97 u11_118
  have u14_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6671 h hv u8_61 u7_97 u11_118
  have u15_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c17067 h a230 u12_13 hv
  have u16_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u2_121 hv u15_112
  have u17_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u2_121 n103 u15_112 hv
  have u18_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u2_121 n103 u15_112 hv
  have u19_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u2_121 u16_109 hv u11_118
  have u20_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8073 h hv u10_54 u9_90 u16_109
  have u21_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7371 h hv u10_54 u9_90 u16_109
  have u22_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u2_121 hv u17_114
  have u23_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u17_114
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u18_116
  have u25_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u18_116 u5_200 hv u6_291
  have u26_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h u25_311 hv
  have u27_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1496 h u25_311 hv
  have u28_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c28415 h u25_311 u12_13 hv
  have u29_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2555 h hv u9_90 u26_94 u7_97
  have u30_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2137 h hv u9_90 u7_97 u27_100
  have u31_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6284 h hv u28_51 u19_115
  have u32_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5924 h hv u28_51 u24_105 u22_107
  have u33_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c211 h hv u29_126 u31_153 u13_158 n162 u20_165 n167
  have u34_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c166 h hv u30_123 u32_150 u14_155 u21_160 n161 n162
  have u35_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c152 h hv u30_123 u32_150 u14_155 u21_160 n161 n162 u34_163
  have u36_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c197 h hv u29_126 u31_153 u13_158 n162 u20_165 n167 u33_169
  exact c17084 h a230 u35_11 u23_12 u36_14

theorem c31440 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → T {1, 3, 9} → False := by
  classical
  intro a237 a230 a49
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
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u6_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25523 h hv u0_2 u4_44 u5_46
  have u7_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12751 h hv u1_37 u4_44 u5_46
  have u8_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7425 h hv u4_44 u5_46 a49
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7565 h hv u4_44 u5_46 a49
  have u10_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8267 h hv u4_44 u5_46 a49
  have u11_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31438 h h0 hv u10_167 u9_162 u8_161 a237 a230
  have u12_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u11_103 hv
  have u13_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv u11_103
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c17066 h a230 u13_13 hv
  have u15_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u2_121 hv u14_112
  have u16_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1879 h u2_121 u11_103 u14_112 hv
  have u17_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1926 h u2_121 u15_109 hv u12_118
  have u18_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18042 h a237 hv u16_114
  have u19_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u16_114
  have u20_310 : Q {3, 5, 7, 9} := by
    by_contra hv
    exact c31335 h h0 u17_115 hv u6_290 u7_199
  exact c28291 h u20_310 u3_1 u18_10 u19_12

theorem c31441 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {0, 2, 5, 8} → T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a112 n162 a103 n237 n198 n196 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u0_121 hv a112
  have u3_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv a112
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1881 h u0_121 a103 a112 hv
  have u5_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1879 h u0_121 a103 a112 hv
  have u6_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1926 h u0_121 u2_109 hv u1_118
  have u7_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u4_116
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv u4_116
  have u9_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u0_121 hv u5_114
  have u10_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u5_114
  have u11_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1813 h u0_121 hv u6_115
  have u12_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18327 h hv u10_12 a103
  have u13_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u3_13 u11_106
  have u14_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c728 h a230 hv n210 u13_234 n237 u12_239 n240
  have u15_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h u14_133 hv a103
  have u16_72 : T {2, 4, 6} := by
    by_contra hv
    exact c3484 h u14_133 hv u5_114
  have u17_29 : T {0, 5, 8} := by
    by_contra hv
    exact c17074 h a230 hv u15_80
  have u18_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9741 h hv u16_72 u8_105 u9_107
  have u19_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4699 h hv u16_72 u8_105 u9_107
  have u20_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c430 h hv u19_141 n162 u18_177 n196 n198 u7_200
  exact c422 h u17_29 u19_141 n162 u18_177 u20_187 n196 n198 u7_200

theorem c31442 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → ¬ T {5, 6, 8} → T {4, 5, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n114 n112 a103 n195 n286 a230
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17066 h a230 hv n112
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u2_121 hv n112
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1674 h hv n112
  have u6_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv n112
  have u7_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c20983 h hv u0_9 a103
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 a103 hv
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c1700 h hv n114
  have u12_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u13_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u2_121 hv n114
  have u14_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1884 h u2_121 n112 n114 hv
  have u15_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u16_29 : T {0, 5, 8} := by
    by_contra hv
    exact c17174 h a230 hv n112 n114
  have u17_78 : T {2, 5, 8} := by
    by_contra hv
    exact c17176 h a230 hv n112 n114
  have u18_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1861 h u2_121 u13_107 u4_109 hv
  have u19_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17487 h hv u3_13 u13_107
  have u20_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9755 h hv u10_54 u13_107 u4_109
  have u21_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22497 h hv u10_54 u13_107 u4_109
  have u22_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u9_90 u13_107 u4_109
  have u23_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15497 h hv u9_90 u13_107 u4_109
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u14_116
  have u25_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u0_9 u14_116
  have u26_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c17089 h a230 u15_12 u3_13 hv
  have u27_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18903 h hv u0_9 u15_12 u3_13
  have u28_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26611 h hv u1_1 u15_12 u3_13
  have u29_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20727 h hv u0_9 u15_12 u3_13
  have u30_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28435 h hv u1_1 u15_12 u3_13
  have u31_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c17083 h a230 hv u15_12 u3_13
  have u32_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17883 h hv u16_29 a103 u14_116
  have u33_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15783 h hv u16_29 a103 u14_116
  have u34_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5003 h hv u17_78 a103 u14_116
  have u35_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u2_121 u18_110 hv
  have u36_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c202 h hv u26_14
  have u37_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c210 h hv u26_14
  have u38_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv u22_141 u23_218 u19_233 u27_243 u6_252 u11_254 u29_256
  have u39_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u20_177 u19_233 u21_268 u28_298 u5_307 u12_309 u30_311
  have u40_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c157 h hv u31_11
  have u41_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c165 h hv u31_11
  have u42_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u35_111 hv n195
  have u43_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6434 h hv u38_57 u24_105
  have u44_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6802 h hv u38_57 u39_93 n114
  have u45_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7234 h hv u38_57 n112 n114
  have u46_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8228 h hv u38_57 u39_93 n114
  have u47_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8508 h hv u38_57 u39_93 n112
  have u48_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1946 h hv u39_93 u8_118
  have u49_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2654 h hv u39_93 u24_105
  have u50_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6942 h hv u38_57 u39_93 n112
  have u51_257 : Q {1, 6, 7, 8} := by
    by_contra hv
    exact c882 h u42_251 u34_143 u33_220 u32_235 u25_245 hv u7_258
  have u52_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c212 h hv u49_127 u43_154 u45_159 u41_163 u46_166 u47_168 u37_169
  have u53_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u50_157 u36_158 u45_159 hv u44_156 u48_122 u40_155
  exact c20868 h u51_257 u53_10 u31_11 u52_15

end BorsukNine.FiniteObstruction

end OAI

import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block157
import OAI.Analysis.MutuallyUnbiased.GramRows.Block158
import OAI.Analysis.MutuallyUnbiased.GramRows.Block159
import OAI.Analysis.MutuallyUnbiased.GramRows.Block160

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17031, row17032, row17033, row17034, row17035, row17036, row17037, row17038, row17039, row17040, row17041, row17042, row17043, row17044, row17045, row17046, row17047, row17048, row17049, row17050]

theorem entryCheck18_0 : entry18_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_0 k)) := by decide +kernel

theorem rowsSound18_0 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval17031 x
  · exact rowEval17032 x
  · exact rowEval17033 x
  · exact rowEval17034 x
  · exact rowEval17035 x
  · exact rowEval17036 x
  · exact rowEval17037 x
  · exact rowEval17038 x
  · exact rowEval17039 x
  · exact rowEval17040 x
  · exact rowEval17041 x
  · exact rowEval17042 x
  · exact rowEval17043 x
  · exact rowEval17044 x
  · exact rowEval17045 x
  · exact rowEval17046 x
  · exact rowEval17047 x
  · exact rowEval17048 x
  · exact rowEval17049 x
  · exact rowEval17050 x

theorem entryEval18_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_0 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck18_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_0]

def rows18_1 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17051, row17052, row17053, row17054, row17055, row17056, row17057, row17058, row17059, row17060, row17061, row17062, row17063, row17064, row17065, row17066, row17067, row17068, row17069, row17070]

theorem entryCheck18_1 : entry18_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_1 k)) := by decide +kernel

theorem rowsSound18_1 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval17051 x
  · exact rowEval17052 x
  · exact rowEval17053 x
  · exact rowEval17054 x
  · exact rowEval17055 x
  · exact rowEval17056 x
  · exact rowEval17057 x
  · exact rowEval17058 x
  · exact rowEval17059 x
  · exact rowEval17060 x
  · exact rowEval17061 x
  · exact rowEval17062 x
  · exact rowEval17063 x
  · exact rowEval17064 x
  · exact rowEval17065 x
  · exact rowEval17066 x
  · exact rowEval17067 x
  · exact rowEval17068 x
  · exact rowEval17069 x
  · exact rowEval17070 x

theorem entryEval18_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_1 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck18_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_1]

def rows18_2 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17071, row17072, row17073, row17074, row17075, row17076, row17077, row17078, row17079, row17080, row17081, row17082, row17083, row17084, row17085, row17086, row17087, row17088, row17089, row17090]

theorem entryCheck18_2 : entry18_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_2 k)) := by decide +kernel

theorem rowsSound18_2 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval17071 x
  · exact rowEval17072 x
  · exact rowEval17073 x
  · exact rowEval17074 x
  · exact rowEval17075 x
  · exact rowEval17076 x
  · exact rowEval17077 x
  · exact rowEval17078 x
  · exact rowEval17079 x
  · exact rowEval17080 x
  · exact rowEval17081 x
  · exact rowEval17082 x
  · exact rowEval17083 x
  · exact rowEval17084 x
  · exact rowEval17085 x
  · exact rowEval17086 x
  · exact rowEval17087 x
  · exact rowEval17088 x
  · exact rowEval17089 x
  · exact rowEval17090 x

theorem entryEval18_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_2 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck18_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_2]

def rows18_3 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17091, row17092, row17093, row17094, row17095, row17096, row17097, row17098, row17099, row17100, row17101, row17102, row17103, row17104, row17105, row17106, row17107, row17108, row17109, row17110]

theorem entryCheck18_3 : entry18_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_3 k)) := by decide +kernel

theorem rowsSound18_3 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval17091 x
  · exact rowEval17092 x
  · exact rowEval17093 x
  · exact rowEval17094 x
  · exact rowEval17095 x
  · exact rowEval17096 x
  · exact rowEval17097 x
  · exact rowEval17098 x
  · exact rowEval17099 x
  · exact rowEval17100 x
  · exact rowEval17101 x
  · exact rowEval17102 x
  · exact rowEval17103 x
  · exact rowEval17104 x
  · exact rowEval17105 x
  · exact rowEval17106 x
  · exact rowEval17107 x
  · exact rowEval17108 x
  · exact rowEval17109 x
  · exact rowEval17110 x

theorem entryEval18_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_3 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck18_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_3]

def rows18_4 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17111, row17112, row17113, row17114, row17115, row17116, row17117, row17118, row17119, row17120, row17121, row17122, row17123, row17124, row17125, row17126, row17127, row17128, row17129, row17130]

theorem entryCheck18_4 : entry18_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_4 k)) := by decide +kernel

theorem rowsSound18_4 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval17111 x
  · exact rowEval17112 x
  · exact rowEval17113 x
  · exact rowEval17114 x
  · exact rowEval17115 x
  · exact rowEval17116 x
  · exact rowEval17117 x
  · exact rowEval17118 x
  · exact rowEval17119 x
  · exact rowEval17120 x
  · exact rowEval17121 x
  · exact rowEval17122 x
  · exact rowEval17123 x
  · exact rowEval17124 x
  · exact rowEval17125 x
  · exact rowEval17126 x
  · exact rowEval17127 x
  · exact rowEval17128 x
  · exact rowEval17129 x
  · exact rowEval17130 x

theorem entryEval18_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_4 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck18_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_4]

def rows18_5 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17131, row17132, row17133, row17134, row17135, row17136, row17137, row17138, row17139, row17140, row17141, row17142, row17143, row17144, row17145, row17146, row17147, row17148, row17149, row17150]

theorem entryCheck18_5 : entry18_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_5 k)) := by decide +kernel

theorem rowsSound18_5 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval17131 x
  · exact rowEval17132 x
  · exact rowEval17133 x
  · exact rowEval17134 x
  · exact rowEval17135 x
  · exact rowEval17136 x
  · exact rowEval17137 x
  · exact rowEval17138 x
  · exact rowEval17139 x
  · exact rowEval17140 x
  · exact rowEval17141 x
  · exact rowEval17142 x
  · exact rowEval17143 x
  · exact rowEval17144 x
  · exact rowEval17145 x
  · exact rowEval17146 x
  · exact rowEval17147 x
  · exact rowEval17148 x
  · exact rowEval17149 x
  · exact rowEval17150 x

theorem entryEval18_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_5 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck18_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_5]

def rows18_6 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17151, row17152, row17153, row17154, row17155, row17156, row17157, row17158, row17159, row17160, row17161, row17162, row17163, row17164, row17165, row17166, row17167, row17168, row17169, row17170]

theorem entryCheck18_6 : entry18_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_6 k)) := by decide +kernel

theorem rowsSound18_6 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval17151 x
  · exact rowEval17152 x
  · exact rowEval17153 x
  · exact rowEval17154 x
  · exact rowEval17155 x
  · exact rowEval17156 x
  · exact rowEval17157 x
  · exact rowEval17158 x
  · exact rowEval17159 x
  · exact rowEval17160 x
  · exact rowEval17161 x
  · exact rowEval17162 x
  · exact rowEval17163 x
  · exact rowEval17164 x
  · exact rowEval17165 x
  · exact rowEval17166 x
  · exact rowEval17167 x
  · exact rowEval17168 x
  · exact rowEval17169 x
  · exact rowEval17170 x

theorem entryEval18_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_6 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck18_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_6]

def rows18_7 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17171, row17172, row17173, row17174, row17175, row17176, row17177, row17178, row17179, row17180, row17181, row17182, row17183, row17184, row17185, row17186, row17187, row17188, row17189, row17190]

theorem entryCheck18_7 : entry18_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_7 k)) := by decide +kernel

theorem rowsSound18_7 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval17171 x
  · exact rowEval17172 x
  · exact rowEval17173 x
  · exact rowEval17174 x
  · exact rowEval17175 x
  · exact rowEval17176 x
  · exact rowEval17177 x
  · exact rowEval17178 x
  · exact rowEval17179 x
  · exact rowEval17180 x
  · exact rowEval17181 x
  · exact rowEval17182 x
  · exact rowEval17183 x
  · exact rowEval17184 x
  · exact rowEval17185 x
  · exact rowEval17186 x
  · exact rowEval17187 x
  · exact rowEval17188 x
  · exact rowEval17189 x
  · exact rowEval17190 x

theorem entryEval18_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_7 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck18_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_7]

def rows18_8 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17191, row17192, row17193, row17194, row17195, row17196, row17197, row17198, row17199, row17200, row17201, row17202, row17203, row17204, row17205, row17206, row17207, row17208, row17209, row17210]

theorem entryCheck18_8 : entry18_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_8 k)) := by decide +kernel

theorem rowsSound18_8 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval17191 x
  · exact rowEval17192 x
  · exact rowEval17193 x
  · exact rowEval17194 x
  · exact rowEval17195 x
  · exact rowEval17196 x
  · exact rowEval17197 x
  · exact rowEval17198 x
  · exact rowEval17199 x
  · exact rowEval17200 x
  · exact rowEval17201 x
  · exact rowEval17202 x
  · exact rowEval17203 x
  · exact rowEval17204 x
  · exact rowEval17205 x
  · exact rowEval17206 x
  · exact rowEval17207 x
  · exact rowEval17208 x
  · exact rowEval17209 x
  · exact rowEval17210 x

theorem entryEval18_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_8 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck18_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_8]

def rows18_9 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17211, row17212, row17213, row17214, row17215, row17216, row17217, row17218, row17219, row17220, row17221, row17222, row17223, row17224, row17225, row17226, row17227, row17228, row17229, row17230]

theorem entryCheck18_9 : entry18_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_9 k)) := by decide +kernel

theorem rowsSound18_9 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval17211 x
  · exact rowEval17212 x
  · exact rowEval17213 x
  · exact rowEval17214 x
  · exact rowEval17215 x
  · exact rowEval17216 x
  · exact rowEval17217 x
  · exact rowEval17218 x
  · exact rowEval17219 x
  · exact rowEval17220 x
  · exact rowEval17221 x
  · exact rowEval17222 x
  · exact rowEval17223 x
  · exact rowEval17224 x
  · exact rowEval17225 x
  · exact rowEval17226 x
  · exact rowEval17227 x
  · exact rowEval17228 x
  · exact rowEval17229 x
  · exact rowEval17230 x

theorem entryEval18_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_9 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck18_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_9]

def rows18_10 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17231, row17232, row17233, row17234, row17235, row17236, row17237, row17238, row17239, row17240, row17241, row17242, row17243, row17244, row17245, row17246, row17247, row17248, row17249, row17250]

theorem entryCheck18_10 : entry18_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_10 k)) := by decide +kernel

theorem rowsSound18_10 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval17231 x
  · exact rowEval17232 x
  · exact rowEval17233 x
  · exact rowEval17234 x
  · exact rowEval17235 x
  · exact rowEval17236 x
  · exact rowEval17237 x
  · exact rowEval17238 x
  · exact rowEval17239 x
  · exact rowEval17240 x
  · exact rowEval17241 x
  · exact rowEval17242 x
  · exact rowEval17243 x
  · exact rowEval17244 x
  · exact rowEval17245 x
  · exact rowEval17246 x
  · exact rowEval17247 x
  · exact rowEval17248 x
  · exact rowEval17249 x
  · exact rowEval17250 x

theorem entryEval18_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_10 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck18_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_10]

def rows18_11 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17251, row17252, row17253, row17254, row17255, row17256, row17257, row17258, row17259, row17260, row17261, row17262, row17263, row17264, row17265, row17266, row17267, row17268, row17269, row17270]

theorem entryCheck18_11 : entry18_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_11 k)) := by decide +kernel

theorem rowsSound18_11 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval17251 x
  · exact rowEval17252 x
  · exact rowEval17253 x
  · exact rowEval17254 x
  · exact rowEval17255 x
  · exact rowEval17256 x
  · exact rowEval17257 x
  · exact rowEval17258 x
  · exact rowEval17259 x
  · exact rowEval17260 x
  · exact rowEval17261 x
  · exact rowEval17262 x
  · exact rowEval17263 x
  · exact rowEval17264 x
  · exact rowEval17265 x
  · exact rowEval17266 x
  · exact rowEval17267 x
  · exact rowEval17268 x
  · exact rowEval17269 x
  · exact rowEval17270 x

theorem entryEval18_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_11 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck18_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_11]

def rows18_12 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17271, row17272, row17273, row17274, row17275, row17276, row17277, row17278, row17279, row17280, row17281, row17282, row17283, row17284, row17285, row17286, row17287, row17288, row17289, row17290]

theorem entryCheck18_12 : entry18_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_12 k)) := by decide +kernel

theorem rowsSound18_12 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval17271 x
  · exact rowEval17272 x
  · exact rowEval17273 x
  · exact rowEval17274 x
  · exact rowEval17275 x
  · exact rowEval17276 x
  · exact rowEval17277 x
  · exact rowEval17278 x
  · exact rowEval17279 x
  · exact rowEval17280 x
  · exact rowEval17281 x
  · exact rowEval17282 x
  · exact rowEval17283 x
  · exact rowEval17284 x
  · exact rowEval17285 x
  · exact rowEval17286 x
  · exact rowEval17287 x
  · exact rowEval17288 x
  · exact rowEval17289 x
  · exact rowEval17290 x

theorem entryEval18_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_12 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck18_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_12]

def rows18_13 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17291, row17292, row17293, row17294, row17295, row17296, row17297, row17298, row17299, row17300, row17301, row17302, row17303, row17304, row17305, row17306, row17307, row17308, row17309, row17310]

theorem entryCheck18_13 : entry18_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_13 k)) := by decide +kernel

theorem rowsSound18_13 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval17291 x
  · exact rowEval17292 x
  · exact rowEval17293 x
  · exact rowEval17294 x
  · exact rowEval17295 x
  · exact rowEval17296 x
  · exact rowEval17297 x
  · exact rowEval17298 x
  · exact rowEval17299 x
  · exact rowEval17300 x
  · exact rowEval17301 x
  · exact rowEval17302 x
  · exact rowEval17303 x
  · exact rowEval17304 x
  · exact rowEval17305 x
  · exact rowEval17306 x
  · exact rowEval17307 x
  · exact rowEval17308 x
  · exact rowEval17309 x
  · exact rowEval17310 x

theorem entryEval18_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_13 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck18_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_13]

def rows18_14 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17311, row17312, row17313, row17314, row17315, row17316, row17317, row17318, row17319, row17320, row17321, row17322, row17323, row17324, row17325, row17326, row17327, row17328, row17329, row17330]

theorem entryCheck18_14 : entry18_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_14 k)) := by decide +kernel

theorem rowsSound18_14 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval17311 x
  · exact rowEval17312 x
  · exact rowEval17313 x
  · exact rowEval17314 x
  · exact rowEval17315 x
  · exact rowEval17316 x
  · exact rowEval17317 x
  · exact rowEval17318 x
  · exact rowEval17319 x
  · exact rowEval17320 x
  · exact rowEval17321 x
  · exact rowEval17322 x
  · exact rowEval17323 x
  · exact rowEval17324 x
  · exact rowEval17325 x
  · exact rowEval17326 x
  · exact rowEval17327 x
  · exact rowEval17328 x
  · exact rowEval17329 x
  · exact rowEval17330 x

theorem entryEval18_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_14 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck18_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_14]

def rows18_15 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17331, row17332, row17333, row17334, row17335, row17336, row17337, row17338, row17339, row17340, row17341, row17342, row17343, row17344, row17345, row17346, row17347, row17348, row17349, row17350]

theorem entryCheck18_15 : entry18_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_15 k)) := by decide +kernel

theorem rowsSound18_15 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval17331 x
  · exact rowEval17332 x
  · exact rowEval17333 x
  · exact rowEval17334 x
  · exact rowEval17335 x
  · exact rowEval17336 x
  · exact rowEval17337 x
  · exact rowEval17338 x
  · exact rowEval17339 x
  · exact rowEval17340 x
  · exact rowEval17341 x
  · exact rowEval17342 x
  · exact rowEval17343 x
  · exact rowEval17344 x
  · exact rowEval17345 x
  · exact rowEval17346 x
  · exact rowEval17347 x
  · exact rowEval17348 x
  · exact rowEval17349 x
  · exact rowEval17350 x

theorem entryEval18_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_15 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck18_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_15]

def rows18_16 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17351, row17352, row17353, row17354, row17355, row17356, row17357, row17358, row17359, row17360, row17361, row17362, row17363, row17364, row17365, row17366, row17367, row17368, row17369, row17370]

theorem entryCheck18_16 : entry18_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_16 k)) := by decide +kernel

theorem rowsSound18_16 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval17351 x
  · exact rowEval17352 x
  · exact rowEval17353 x
  · exact rowEval17354 x
  · exact rowEval17355 x
  · exact rowEval17356 x
  · exact rowEval17357 x
  · exact rowEval17358 x
  · exact rowEval17359 x
  · exact rowEval17360 x
  · exact rowEval17361 x
  · exact rowEval17362 x
  · exact rowEval17363 x
  · exact rowEval17364 x
  · exact rowEval17365 x
  · exact rowEval17366 x
  · exact rowEval17367 x
  · exact rowEval17368 x
  · exact rowEval17369 x
  · exact rowEval17370 x

theorem entryEval18_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_16 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck18_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_16]

def rows18_17 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17371, row17372, row17373, row17374, row17375, row17376, row17377, row17378, row17379, row17380, row17381, row17382, row17383, row17384, row17385, row17386, row17387, row17388, row17389, row17390]

theorem entryCheck18_17 : entry18_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_17 k)) := by decide +kernel

theorem rowsSound18_17 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form17) x := by
  fin_cases k
  · exact rowEval17371 x
  · exact rowEval17372 x
  · exact rowEval17373 x
  · exact rowEval17374 x
  · exact rowEval17375 x
  · exact rowEval17376 x
  · exact rowEval17377 x
  · exact rowEval17378 x
  · exact rowEval17379 x
  · exact rowEval17380 x
  · exact rowEval17381 x
  · exact rowEval17382 x
  · exact rowEval17383 x
  · exact rowEval17384 x
  · exact rowEval17385 x
  · exact rowEval17386 x
  · exact rowEval17387 x
  · exact rowEval17388 x
  · exact rowEval17389 x
  · exact rowEval17390 x

theorem entryEval18_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_17 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form17 B := by
  rw [entryCheck18_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_17]

def rows18_18 : Fin GramFunctions.Block4.form18.size → Integer.Sparse Key := ![row17391, row17392, row17393, row17394, row17395, row17396, row17397, row17398, row17399, row17400, row17401, row17402, row17403, row17404, row17405, row17406, row17407, row17408, row17409, row17410]

theorem entryCheck18_18 : entry18_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form18.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form18.terms k).coefficient) (rows18_18 k)) := by decide +kernel

theorem rowsSound18_18 (k : Fin GramFunctions.Block4.form18.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows18_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form18.terms k).tag (GramFunctions.Block4.form18.terms k).charge GramFunctions.Block4.form18) x := by
  fin_cases k
  · exact rowEval17391 x
  · exact rowEval17392 x
  · exact rowEval17393 x
  · exact rowEval17394 x
  · exact rowEval17395 x
  · exact rowEval17396 x
  · exact rowEval17397 x
  · exact rowEval17398 x
  · exact rowEval17399 x
  · exact rowEval17400 x
  · exact rowEval17401 x
  · exact rowEval17402 x
  · exact rowEval17403 x
  · exact rowEval17404 x
  · exact rowEval17405 x
  · exact rowEval17406 x
  · exact rowEval17407 x
  · exact rowEval17408 x
  · exact rowEval17409 x
  · exact rowEval17410 x

theorem entryEval18_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry18_18 (GramNormalization.eval B) = GramFunctions.Block4.form18.mixedGram GramFunctions.Block4.form18 B := by
  rw [entryCheck18_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form18 GramFunctions.Block4.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound18_18]

end MUB6.Certificate.GramEntries.Block4

end OAI

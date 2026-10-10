import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block91
import OAI.Analysis.MutuallyUnbiased.GramRows.Block92
import OAI.Analysis.MutuallyUnbiased.GramRows.Block95
import OAI.Analysis.MutuallyUnbiased.GramRows.Block96
import OAI.Analysis.MutuallyUnbiased.GramRows.Block97

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8661, row8662, row8663, row8664, row9173, row9174, row9175, row9176, row9177, row9178, row9179, row9180, row9181, row9182, row9183, row9184]

theorem entryCheck15_0 : entry15_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_0 k)) := by decide +kernel

theorem rowsSound15_0 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval8661 x
  · exact rowEval8662 x
  · exact rowEval8663 x
  · exact rowEval8664 x
  · exact rowEval9173 x
  · exact rowEval9174 x
  · exact rowEval9175 x
  · exact rowEval9176 x
  · exact rowEval9177 x
  · exact rowEval9178 x
  · exact rowEval9179 x
  · exact rowEval9180 x
  · exact rowEval9181 x
  · exact rowEval9182 x
  · exact rowEval9183 x
  · exact rowEval9184 x

theorem entryEval15_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_0 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck15_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_0]

def rows15_1 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8669, row8670, row8671, row8672, row9185, row9186, row9187, row9188, row9189, row9190, row9191, row9192, row9193, row9194, row9195, row9196]

theorem entryCheck15_1 : entry15_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_1 k)) := by decide +kernel

theorem rowsSound15_1 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval8669 x
  · exact rowEval8670 x
  · exact rowEval8671 x
  · exact rowEval8672 x
  · exact rowEval9185 x
  · exact rowEval9186 x
  · exact rowEval9187 x
  · exact rowEval9188 x
  · exact rowEval9189 x
  · exact rowEval9190 x
  · exact rowEval9191 x
  · exact rowEval9192 x
  · exact rowEval9193 x
  · exact rowEval9194 x
  · exact rowEval9195 x
  · exact rowEval9196 x

theorem entryEval15_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_1 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck15_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_1]

def rows15_2 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8677, row8678, row8679, row8680, row9197, row9198, row9199, row9200, row9201, row9202, row9203, row9204, row9205, row9206, row9207, row9208]

theorem entryCheck15_2 : entry15_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_2 k)) := by decide +kernel

theorem rowsSound15_2 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8677 x
  · exact rowEval8678 x
  · exact rowEval8679 x
  · exact rowEval8680 x
  · exact rowEval9197 x
  · exact rowEval9198 x
  · exact rowEval9199 x
  · exact rowEval9200 x
  · exact rowEval9201 x
  · exact rowEval9202 x
  · exact rowEval9203 x
  · exact rowEval9204 x
  · exact rowEval9205 x
  · exact rowEval9206 x
  · exact rowEval9207 x
  · exact rowEval9208 x

theorem entryEval15_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_2 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck15_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_2]

def rows15_3 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8685, row8686, row8687, row8688, row9209, row9210, row9211, row9212, row9213, row9214, row9215, row9216, row9217, row9218, row9219, row9220]

theorem entryCheck15_3 : entry15_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_3 k)) := by decide +kernel

theorem rowsSound15_3 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8685 x
  · exact rowEval8686 x
  · exact rowEval8687 x
  · exact rowEval8688 x
  · exact rowEval9209 x
  · exact rowEval9210 x
  · exact rowEval9211 x
  · exact rowEval9212 x
  · exact rowEval9213 x
  · exact rowEval9214 x
  · exact rowEval9215 x
  · exact rowEval9216 x
  · exact rowEval9217 x
  · exact rowEval9218 x
  · exact rowEval9219 x
  · exact rowEval9220 x

theorem entryEval15_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_3 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck15_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_3]

def rows15_4 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8693, row8694, row8695, row8696, row9221, row9222, row9223, row9224, row9225, row9226, row9227, row9228, row9229, row9230, row9231, row9232]

theorem entryCheck15_4 : entry15_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_4 k)) := by decide +kernel

theorem rowsSound15_4 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8693 x
  · exact rowEval8694 x
  · exact rowEval8695 x
  · exact rowEval8696 x
  · exact rowEval9221 x
  · exact rowEval9222 x
  · exact rowEval9223 x
  · exact rowEval9224 x
  · exact rowEval9225 x
  · exact rowEval9226 x
  · exact rowEval9227 x
  · exact rowEval9228 x
  · exact rowEval9229 x
  · exact rowEval9230 x
  · exact rowEval9231 x
  · exact rowEval9232 x

theorem entryEval15_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_4 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck15_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_4]

def rows15_5 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8701, row8702, row8703, row8704, row9233, row9234, row9235, row9236, row9237, row9238, row9239, row9240, row9241, row9242, row9243, row9244]

theorem entryCheck15_5 : entry15_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_5 k)) := by decide +kernel

theorem rowsSound15_5 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8701 x
  · exact rowEval8702 x
  · exact rowEval8703 x
  · exact rowEval8704 x
  · exact rowEval9233 x
  · exact rowEval9234 x
  · exact rowEval9235 x
  · exact rowEval9236 x
  · exact rowEval9237 x
  · exact rowEval9238 x
  · exact rowEval9239 x
  · exact rowEval9240 x
  · exact rowEval9241 x
  · exact rowEval9242 x
  · exact rowEval9243 x
  · exact rowEval9244 x

theorem entryEval15_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_5 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck15_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_5]

def rows15_6 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8709, row8710, row8711, row8712, row9245, row9246, row9247, row9248, row9249, row9250, row9251, row9252, row9253, row9254, row9255, row9256]

theorem entryCheck15_6 : entry15_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_6 k)) := by decide +kernel

theorem rowsSound15_6 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8709 x
  · exact rowEval8710 x
  · exact rowEval8711 x
  · exact rowEval8712 x
  · exact rowEval9245 x
  · exact rowEval9246 x
  · exact rowEval9247 x
  · exact rowEval9248 x
  · exact rowEval9249 x
  · exact rowEval9250 x
  · exact rowEval9251 x
  · exact rowEval9252 x
  · exact rowEval9253 x
  · exact rowEval9254 x
  · exact rowEval9255 x
  · exact rowEval9256 x

theorem entryEval15_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_6 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck15_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_6]

def rows15_7 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8717, row8718, row8719, row8720, row9257, row9258, row9259, row9260, row9261, row9262, row9263, row9264, row9265, row9266, row9267, row9268]

theorem entryCheck15_7 : entry15_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_7 k)) := by decide +kernel

theorem rowsSound15_7 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8717 x
  · exact rowEval8718 x
  · exact rowEval8719 x
  · exact rowEval8720 x
  · exact rowEval9257 x
  · exact rowEval9258 x
  · exact rowEval9259 x
  · exact rowEval9260 x
  · exact rowEval9261 x
  · exact rowEval9262 x
  · exact rowEval9263 x
  · exact rowEval9264 x
  · exact rowEval9265 x
  · exact rowEval9266 x
  · exact rowEval9267 x
  · exact rowEval9268 x

theorem entryEval15_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_7 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck15_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_7]

def rows15_8 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8725, row8726, row8727, row8728, row9269, row9270, row9271, row9272, row9273, row9274, row9275, row9276, row9277, row9278, row9279, row9280]

theorem entryCheck15_8 : entry15_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_8 k)) := by decide +kernel

theorem rowsSound15_8 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8725 x
  · exact rowEval8726 x
  · exact rowEval8727 x
  · exact rowEval8728 x
  · exact rowEval9269 x
  · exact rowEval9270 x
  · exact rowEval9271 x
  · exact rowEval9272 x
  · exact rowEval9273 x
  · exact rowEval9274 x
  · exact rowEval9275 x
  · exact rowEval9276 x
  · exact rowEval9277 x
  · exact rowEval9278 x
  · exact rowEval9279 x
  · exact rowEval9280 x

theorem entryEval15_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_8 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck15_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_8]

def rows15_9 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8733, row8734, row8735, row8736, row9281, row9282, row9283, row9284, row9285, row9286, row9287, row9288, row9289, row9290, row9291, row9292]

theorem entryCheck15_9 : entry15_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_9 k)) := by decide +kernel

theorem rowsSound15_9 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8733 x
  · exact rowEval8734 x
  · exact rowEval8735 x
  · exact rowEval8736 x
  · exact rowEval9281 x
  · exact rowEval9282 x
  · exact rowEval9283 x
  · exact rowEval9284 x
  · exact rowEval9285 x
  · exact rowEval9286 x
  · exact rowEval9287 x
  · exact rowEval9288 x
  · exact rowEval9289 x
  · exact rowEval9290 x
  · exact rowEval9291 x
  · exact rowEval9292 x

theorem entryEval15_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_9 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck15_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_9]

def rows15_10 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8741, row8742, row8743, row8744, row9293, row9294, row9295, row9296, row9297, row9298, row9299, row9300, row9301, row9302, row9303, row9304]

theorem entryCheck15_10 : entry15_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_10 k)) := by decide +kernel

theorem rowsSound15_10 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval8741 x
  · exact rowEval8742 x
  · exact rowEval8743 x
  · exact rowEval8744 x
  · exact rowEval9293 x
  · exact rowEval9294 x
  · exact rowEval9295 x
  · exact rowEval9296 x
  · exact rowEval9297 x
  · exact rowEval9298 x
  · exact rowEval9299 x
  · exact rowEval9300 x
  · exact rowEval9301 x
  · exact rowEval9302 x
  · exact rowEval9303 x
  · exact rowEval9304 x

theorem entryEval15_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_10 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck15_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_10]

def rows15_11 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row8749, row8750, row8751, row8752, row9305, row9306, row9307, row9308, row9309, row9310, row9311, row9312, row9313, row9314, row9315, row9316]

theorem entryCheck15_11 : entry15_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_11 k)) := by decide +kernel

theorem rowsSound15_11 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval8749 x
  · exact rowEval8750 x
  · exact rowEval8751 x
  · exact rowEval8752 x
  · exact rowEval9305 x
  · exact rowEval9306 x
  · exact rowEval9307 x
  · exact rowEval9308 x
  · exact rowEval9309 x
  · exact rowEval9310 x
  · exact rowEval9311 x
  · exact rowEval9312 x
  · exact rowEval9313 x
  · exact rowEval9314 x
  · exact rowEval9315 x
  · exact rowEval9316 x

theorem entryEval15_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_11 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck15_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_11]

def rows15_12 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9317, row9318, row9319, row9320, row9321, row9322, row9323, row9324, row9325, row9326, row9327, row9328, row9329, row9330, row9331, row9332]

theorem entryCheck15_12 : entry15_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_12 k)) := by decide +kernel

theorem rowsSound15_12 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval9317 x
  · exact rowEval9318 x
  · exact rowEval9319 x
  · exact rowEval9320 x
  · exact rowEval9321 x
  · exact rowEval9322 x
  · exact rowEval9323 x
  · exact rowEval9324 x
  · exact rowEval9325 x
  · exact rowEval9326 x
  · exact rowEval9327 x
  · exact rowEval9328 x
  · exact rowEval9329 x
  · exact rowEval9330 x
  · exact rowEval9331 x
  · exact rowEval9332 x

theorem entryEval15_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_12 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck15_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_12]

def rows15_13 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9333, row9334, row9335, row9336, row9337, row9338, row9339, row9340, row9341, row9342, row9343, row9344, row9345, row9346, row9347, row9348]

theorem entryCheck15_13 : entry15_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_13 k)) := by decide +kernel

theorem rowsSound15_13 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval9333 x
  · exact rowEval9334 x
  · exact rowEval9335 x
  · exact rowEval9336 x
  · exact rowEval9337 x
  · exact rowEval9338 x
  · exact rowEval9339 x
  · exact rowEval9340 x
  · exact rowEval9341 x
  · exact rowEval9342 x
  · exact rowEval9343 x
  · exact rowEval9344 x
  · exact rowEval9345 x
  · exact rowEval9346 x
  · exact rowEval9347 x
  · exact rowEval9348 x

theorem entryEval15_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_13 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck15_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_13]

def rows15_14 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9349, row9350, row9351, row9352, row9353, row9354, row9355, row9356, row9357, row9358, row9359, row9360, row9361, row9362, row9363, row9364]

theorem entryCheck15_14 : entry15_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_14 k)) := by decide +kernel

theorem rowsSound15_14 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval9349 x
  · exact rowEval9350 x
  · exact rowEval9351 x
  · exact rowEval9352 x
  · exact rowEval9353 x
  · exact rowEval9354 x
  · exact rowEval9355 x
  · exact rowEval9356 x
  · exact rowEval9357 x
  · exact rowEval9358 x
  · exact rowEval9359 x
  · exact rowEval9360 x
  · exact rowEval9361 x
  · exact rowEval9362 x
  · exact rowEval9363 x
  · exact rowEval9364 x

theorem entryEval15_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_14 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck15_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_14]

def rows15_15 : Fin GramFunctions.Block3.form15.size → Integer.Sparse Key := ![row9365, row9366, row9367, row9368, row9369, row9370, row9371, row9372, row9373, row9374, row9375, row9376, row9377, row9378, row9379, row9380]

theorem entryCheck15_15 : entry15_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form15.terms k).coefficient) (rows15_15 k)) := by decide +kernel

theorem rowsSound15_15 (k : Fin GramFunctions.Block3.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form15.terms k).tag (GramFunctions.Block3.form15.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval9365 x
  · exact rowEval9366 x
  · exact rowEval9367 x
  · exact rowEval9368 x
  · exact rowEval9369 x
  · exact rowEval9370 x
  · exact rowEval9371 x
  · exact rowEval9372 x
  · exact rowEval9373 x
  · exact rowEval9374 x
  · exact rowEval9375 x
  · exact rowEval9376 x
  · exact rowEval9377 x
  · exact rowEval9378 x
  · exact rowEval9379 x
  · exact rowEval9380 x

theorem entryEval15_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_15 (GramNormalization.eval B) = GramFunctions.Block3.form15.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck15_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form15 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_15]

end MUB6.Certificate.GramEntries.Block3

end OAI

import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block82
import OAI.Analysis.MutuallyUnbiased.GramRows.Block83

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row7498, row7499, row7500, row7501, row7502, row7503, row7504, row7505, row7506, row7507, row7508, row7509]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7494 x
  · exact rowEval7495 x
  · exact rowEval7496 x
  · exact rowEval7497 x
  · exact rowEval7498 x
  · exact rowEval7499 x
  · exact rowEval7500 x
  · exact rowEval7501 x
  · exact rowEval7502 x
  · exact rowEval7503 x
  · exact rowEval7504 x
  · exact rowEval7505 x
  · exact rowEval7506 x
  · exact rowEval7507 x
  · exact rowEval7508 x
  · exact rowEval7509 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row7514, row7515, row7516, row7517, row7518, row7519, row7520, row7521, row7522, row7523, row7524, row7525]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7510 x
  · exact rowEval7511 x
  · exact rowEval7512 x
  · exact rowEval7513 x
  · exact rowEval7514 x
  · exact rowEval7515 x
  · exact rowEval7516 x
  · exact rowEval7517 x
  · exact rowEval7518 x
  · exact rowEval7519 x
  · exact rowEval7520 x
  · exact rowEval7521 x
  · exact rowEval7522 x
  · exact rowEval7523 x
  · exact rowEval7524 x
  · exact rowEval7525 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row7530, row7531, row7532, row7533, row7534, row7535, row7536, row7537, row7538, row7539, row7540, row7541]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7526 x
  · exact rowEval7527 x
  · exact rowEval7528 x
  · exact rowEval7529 x
  · exact rowEval7530 x
  · exact rowEval7531 x
  · exact rowEval7532 x
  · exact rowEval7533 x
  · exact rowEval7534 x
  · exact rowEval7535 x
  · exact rowEval7536 x
  · exact rowEval7537 x
  · exact rowEval7538 x
  · exact rowEval7539 x
  · exact rowEval7540 x
  · exact rowEval7541 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row7546, row7547, row7548, row7549, row7550, row7551, row7552, row7553, row7554, row7555, row7556, row7557]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7542 x
  · exact rowEval7543 x
  · exact rowEval7544 x
  · exact rowEval7545 x
  · exact rowEval7546 x
  · exact rowEval7547 x
  · exact rowEval7548 x
  · exact rowEval7549 x
  · exact rowEval7550 x
  · exact rowEval7551 x
  · exact rowEval7552 x
  · exact rowEval7553 x
  · exact rowEval7554 x
  · exact rowEval7555 x
  · exact rowEval7556 x
  · exact rowEval7557 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row7562, row7563, row7564, row7565, row7566, row7567, row7568, row7569, row7570, row7571, row7572, row7573]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block3.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form4.terms k).tag (GramFunctions.Block3.form4.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval7558 x
  · exact rowEval7559 x
  · exact rowEval7560 x
  · exact rowEval7561 x
  · exact rowEval7562 x
  · exact rowEval7563 x
  · exact rowEval7564 x
  · exact rowEval7565 x
  · exact rowEval7566 x
  · exact rowEval7567 x
  · exact rowEval7568 x
  · exact rowEval7569 x
  · exact rowEval7570 x
  · exact rowEval7571 x
  · exact rowEval7572 x
  · exact rowEval7573 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block3.form4.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form4 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block3

end OAI

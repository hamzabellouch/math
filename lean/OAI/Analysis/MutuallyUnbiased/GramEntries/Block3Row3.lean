import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block82

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7430, row7431, row7432, row7433, row7434, row7435, row7436, row7437, row7438, row7439, row7440, row7441, row7442, row7443, row7444, row7445]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7430 x
  · exact rowEval7431 x
  · exact rowEval7432 x
  · exact rowEval7433 x
  · exact rowEval7434 x
  · exact rowEval7435 x
  · exact rowEval7436 x
  · exact rowEval7437 x
  · exact rowEval7438 x
  · exact rowEval7439 x
  · exact rowEval7440 x
  · exact rowEval7441 x
  · exact rowEval7442 x
  · exact rowEval7443 x
  · exact rowEval7444 x
  · exact rowEval7445 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7446, row7447, row7448, row7449, row7450, row7451, row7452, row7453, row7454, row7455, row7456, row7457, row7458, row7459, row7460, row7461]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7446 x
  · exact rowEval7447 x
  · exact rowEval7448 x
  · exact rowEval7449 x
  · exact rowEval7450 x
  · exact rowEval7451 x
  · exact rowEval7452 x
  · exact rowEval7453 x
  · exact rowEval7454 x
  · exact rowEval7455 x
  · exact rowEval7456 x
  · exact rowEval7457 x
  · exact rowEval7458 x
  · exact rowEval7459 x
  · exact rowEval7460 x
  · exact rowEval7461 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7462, row7463, row7464, row7465, row7466, row7467, row7468, row7469, row7470, row7471, row7472, row7473, row7474, row7475, row7476, row7477]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7462 x
  · exact rowEval7463 x
  · exact rowEval7464 x
  · exact rowEval7465 x
  · exact rowEval7466 x
  · exact rowEval7467 x
  · exact rowEval7468 x
  · exact rowEval7469 x
  · exact rowEval7470 x
  · exact rowEval7471 x
  · exact rowEval7472 x
  · exact rowEval7473 x
  · exact rowEval7474 x
  · exact rowEval7475 x
  · exact rowEval7476 x
  · exact rowEval7477 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7478, row7479, row7480, row7481, row7482, row7483, row7484, row7485, row7486, row7487, row7488, row7489, row7490, row7491, row7492, row7493]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block3.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form3.terms k).tag (GramFunctions.Block3.form3.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval7478 x
  · exact rowEval7479 x
  · exact rowEval7480 x
  · exact rowEval7481 x
  · exact rowEval7482 x
  · exact rowEval7483 x
  · exact rowEval7484 x
  · exact rowEval7485 x
  · exact rowEval7486 x
  · exact rowEval7487 x
  · exact rowEval7488 x
  · exact rowEval7489 x
  · exact rowEval7490 x
  · exact rowEval7491 x
  · exact rowEval7492 x
  · exact rowEval7493 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block3.form3.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form3 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block3

end OAI

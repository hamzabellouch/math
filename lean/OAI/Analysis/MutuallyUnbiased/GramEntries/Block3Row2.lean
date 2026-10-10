import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81
import OAI.Analysis.MutuallyUnbiased.GramRows.Block82

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row7386, row7387, row7388, row7389, row7390, row7391, row7392, row7393, row7394, row7395, row7396, row7397]

theorem entryCheck2_0 : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

theorem rowsSound2_0 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7382 x
  · exact rowEval7383 x
  · exact rowEval7384 x
  · exact rowEval7385 x
  · exact rowEval7386 x
  · exact rowEval7387 x
  · exact rowEval7388 x
  · exact rowEval7389 x
  · exact rowEval7390 x
  · exact rowEval7391 x
  · exact rowEval7392 x
  · exact rowEval7393 x
  · exact rowEval7394 x
  · exact rowEval7395 x
  · exact rowEval7396 x
  · exact rowEval7397 x

theorem entryEval2_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_0 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck2_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_0]

def rows2_1 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row7402, row7403, row7404, row7405, row7406, row7407, row7408, row7409, row7410, row7411, row7412, row7413]

theorem entryCheck2_1 : entry2_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_1 k)) := by decide +kernel

theorem rowsSound2_1 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7398 x
  · exact rowEval7399 x
  · exact rowEval7400 x
  · exact rowEval7401 x
  · exact rowEval7402 x
  · exact rowEval7403 x
  · exact rowEval7404 x
  · exact rowEval7405 x
  · exact rowEval7406 x
  · exact rowEval7407 x
  · exact rowEval7408 x
  · exact rowEval7409 x
  · exact rowEval7410 x
  · exact rowEval7411 x
  · exact rowEval7412 x
  · exact rowEval7413 x

theorem entryEval2_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_1 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck2_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_1]

def rows2_2 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row7418, row7419, row7420, row7421, row7422, row7423, row7424, row7425, row7426, row7427, row7428, row7429]

theorem entryCheck2_2 : entry2_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form2.terms k).coefficient) (rows2_2 k)) := by decide +kernel

theorem rowsSound2_2 (k : Fin GramFunctions.Block3.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form2.terms k).tag (GramFunctions.Block3.form2.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval7414 x
  · exact rowEval7415 x
  · exact rowEval7416 x
  · exact rowEval7417 x
  · exact rowEval7418 x
  · exact rowEval7419 x
  · exact rowEval7420 x
  · exact rowEval7421 x
  · exact rowEval7422 x
  · exact rowEval7423 x
  · exact rowEval7424 x
  · exact rowEval7425 x
  · exact rowEval7426 x
  · exact rowEval7427 x
  · exact rowEval7428 x
  · exact rowEval7429 x

theorem entryEval2_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry2_2 (GramNormalization.eval B) = GramFunctions.Block3.form2.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck2_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form2 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound2_2]

end MUB6.Certificate.GramEntries.Block3

end OAI

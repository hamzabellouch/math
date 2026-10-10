import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalElimination
import OAI.Analysis.MatrixSigning.Matrices.PivotRowLoop

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W07

def foundIndex (o : Outcome) : Option ℕ := if o.found then some o.index else none

theorem foundIndex_outcome {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    foundIndex (outcome M a k) =
      (List.range' a k).find? (fun i => decide (entry M i ≠ 0)) := by
  induction k generalizing a with
  | zero => simp [outcome,foundIndex]
  | succ k ih =>
    by_cases hz : entry M a = 0
    · simp only [outcome, hz, ite_true]
      rw [ih]
      simp [List.range'_succ, hz]
    · simp [outcome, hz, foundIndex, List.range'_succ]

theorem successor_finRange (n : ℕ) :
    (List.finRange n).map (fun j => j.succ.val) = List.range' 1 n := by
  calc
    _ = ((List.finRange n).map Fin.val).map (fun j => j+1) := by
      simp only [List.map_map,Function.comp_def,Fin.val_succ]
    _ = (List.range n).map (fun j => j+1) := by rw [List.map_coe_finRange_eq_range]
    _ = List.range' 1 n := by rw [List.range_eq_range',← List.range'_succ_left]

theorem offDiagonal_outcome {n : ℕ} (M : DenseRatMatrix (n+1)) :
    foundIndex (outcome M 1 n) =
      (firstNonzeroOffDiagonal (DenseRatMatrix.decode M)).map (fun j => j.succ.val) := by
  rw [foundIndex_outcome,← successor_finRange]
  rw [List.find?_map]
  congr 1
  unfold firstNonzeroOffDiagonal
  congr 1
  funext j
  have hj : j.succ.val < n+1 := j.succ.isLt
  have he : (⟨j.succ.val, hj⟩ : Fin (n+1)) = j.succ := Fin.ext rfl
  change decide (entry M j.succ.val ≠ 0) = decide (DenseRatMatrix.decode M 0 j.succ ≠ 0)
  simp only [entry, dite_eq_left hj, he]

theorem outcome_bounds {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) :
    a ≤ (outcome M a k).index ∧ (outcome M a k).index ≤ a+k ∧
      (outcome M a k).remaining ≤ k := by
  induction k generalizing a with
  | zero => simp [outcome]
  | succ k ih =>
    by_cases hz : entry M a = 0
    · have h := ih (a+1)
      simp only [outcome,hz,ite_true]
      omega
    · simp [outcome,hz]

end KS.W17.PivotRowLoop

end

end OAI

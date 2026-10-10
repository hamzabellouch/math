import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.UniformElimination
import OAI.Analysis.MatrixSigning.Matrices.EliminationCallBounds

namespace OAI

section

namespace KS.W17
open KS.W07

theorem pivotTerminal_none_cases {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (ht : pivotTerminal M = none) :
    (M 0 0 = 0 ∧ firstNonzeroOffDiagonal M = none) ∨ 0 < M 0 0 := by
  have hn : ¬ M 0 0 < 0 := by
    intro h
    simp [pivotTerminal,h] at ht
  by_cases hz : M 0 0 = 0
  · left
    refine ⟨hz,?_⟩
    cases hf : firstNonzeroOffDiagonal M with
    | none => rfl
    | some j => simp [pivotTerminal,hz,hf] at ht
  · right
    exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hz)

theorem DenseEliminationCall.uniform_child {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} (h : DenseEliminationCall A M)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    DenseEliminationCall A (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode M))) := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · rw [schurTail_zero_pivot _ hz]
    exact .zero h hz hr
  · exact .positive h hp

theorem DenseEliminationCall.uniform_child_parts {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} (h : DenseEliminationCall A M)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b) (i j : Fin n) :
    Nat.size (schurTail (DenseRatMatrix.decode M) i j).num.natAbs ≤ KS.W30.inverseBitBound N b ∧
      Nat.size (schurTail (DenseRatMatrix.decode M) i j).den ≤ KS.W30.inverseBitBound N b := by
  simpa using (h.uniform_child ht).entry_parts_size_le b hnum hden i j

end KS.W17

end

end OAI

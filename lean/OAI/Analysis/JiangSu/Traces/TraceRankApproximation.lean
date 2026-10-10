import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.MatrixRanks

namespace OAI

section

namespace Pureness
open scoped ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem trace_rank_approximation (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (p : A) (hp : 0 ≤ p) (η : ℝ) (hη : 0 < η) :
    ∃ l : ℕ, ∃ w : CStarMatrix (Fin (l + 1)) (Fin (l + 1)) A,
      0 ≤ w ∧ ∀ τ : TracialState A,
        0 ≤ (τ.functional p).re - (matrixRank τ w).toReal ∧
        (τ.functional p).re - (matrixRank τ w).toReal ≤ η := by
  obtain ⟨c, l, hc, hl, hcuts, happrox⟩ :=
    exists_integer_cut_rank_approximation hsimple hinf hT p hp η hη
  have hl0 : 0 < l := by exact_mod_cast (norm_nonneg c).trans_lt hl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl0.ne'
  refine ⟨k, diagonalMatrixHom (fun i : Fin (k + 1) => positiveIntegerCut c i),
    diagonalMatrix_nonneg _ (fun i => hcuts i), ?_⟩
  intro τ
  rw [matrixRank_diagonal_toReal τ (fun i : Fin (k + 1) => positiveIntegerCut c i)
    (fun i => hcuts i)]
  have hs := Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (normalizedRootRank τ (positiveIntegerCut c j)).toReal) (k + 1)
  rw [hs]
  exact ⟨(happrox τ).1, (happrox τ).2.le⟩

end Pureness
end

end OAI

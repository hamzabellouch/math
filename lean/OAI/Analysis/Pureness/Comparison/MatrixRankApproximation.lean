import OAI.Analysis.Pureness.Comparison.MatrixDiagonal
import OAI.Analysis.Pureness.Comparison.RankCutFamily
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
open scoped BigOperators
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [IsSimpleCStarAlgebra A]

theorem exists_matrix_rank_approximation
    (hinfinite : ¬ FiniteDimensional ℂ A) {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ M : CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A, ∃ hM : 0 ≤ M,
      ∀ τ : TracialState A,
        (τ.toPositiveLinearMap b).re - δ < (τ.matrixSupportMass M hM).toReal ∧
        (τ.matrixSupportMass M hM).toReal ≤ (τ.toPositiveLinearMap b).re := by
  obtain ⟨L, hL, v, hv, hbound⟩ := exists_rank_approximating_cut_family hinfinite hb hδ
  cases L with
  | zero => omega
  | succ n =>
    let w : Fin (n + 1) → A := fun i => v i.val
    have hw : ∀ i, 0 ≤ w i := fun i => hv i.val
    refine ⟨n, matrixDiagonalHom w, matrixDiagonal_nonneg w hw, fun τ => ?_⟩
    rw [τ.matrixSupportMass_diagonal w hw]
    have heq : (∑ i : Fin (n + 1), (τ.spectralSupportMass (w i) (hw i)).toReal) =
        ∑ j ∈ Finset.range (n + 1), (τ.spectralSupportMass (v j) (hv j)).toReal := by
      exact Fin.sum_univ_eq_sum_range (fun j => (τ.spectralSupportMass (v j) (hv j)).toReal) (n + 1)
    rw [heq]
    exact hbound τ
end CuntzComparison

end OAI

import OAI.Analysis.Pureness.Completion.CompletedSourceLowerBound
import OAI.Analysis.Pureness.Traces.TraceRankApproximation

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def shrinkPositive (w : A) (δ : ℝ) : A := (δ / max 1 ‖w‖) • w

lemma shrinkPositive_nonneg (w : A) (hw : 0 ≤ w) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ shrinkPositive w δ :=
  smul_nonneg (div_pos hδ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).le hw

omit [PartialOrder A] [StarOrderedRing A] in
lemma shrinkPositive_norm_le (w : A) (δ : ℝ) (hδ : 0 < δ) : ‖shrinkPositive w δ‖ ≤ δ := by
  have ht : 0 < δ / max 1 ‖w‖ := div_pos hδ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  rw [shrinkPositive, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ δ / max 1 ‖w‖ * max 1 ‖w‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht.le
    _ = δ := div_mul_cancel₀ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

lemma shrinkPositive_rank (τ : TracialState A) (w : A) (δ : ℝ) (hδ : 0 < δ) :
    normalizedRootRank τ (shrinkPositive w δ) = normalizedRootRank τ w :=
  normalizedRootRank_smul τ w _ (div_pos hδ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

lemma exists_small_matrix_same_rank {k : ℕ} [NeZero k] (w : MatrixStage A k)
    (hw : 0 ≤ w) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : MatrixStage A k, 0 ≤ v ∧ ‖v‖ ≤ δ ∧ ∀ τ : TracialState A, matrixRank τ v = matrixRank τ w := by
  refine ⟨shrinkPositive w δ, shrinkPositive_nonneg w hw δ hδ, shrinkPositive_norm_le w δ hδ, ?_⟩
  intro τ
  unfold matrixRank
  rw [shrinkPositive_rank _ w δ hδ]

theorem exists_completed_increment_approximants (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (a : CornerCompletion A) (ha : 0 ≤ a) (s : ℝ) (hs : 0 ≤ s)
    (η δ : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hδ : ∀ j, 0 < δ j) :
    ∃ l : ℕ → ℕ, ∃ w : (j : ℕ) → MatrixStage A (l j + 1),
      (∀ j, 0 ≤ w j) ∧ (∀ j, ‖w j‖ ≤ δ j) ∧
      ∀ j, ∀ τ : TracialState A,
        0 ≤ s * (τ.functional (completedSourceU a (j + 1))).re -
          s * (τ.functional (completedSourceU a j)).re - (matrixRank τ (w j)).toReal ∧
        s * (τ.functional (completedSourceU a (j + 1))).re -
          s * (τ.functional (completedSourceU a j)).re - (matrixRank τ (w j)).toReal ≤ η j := by
  have hex (j : ℕ) : ∃ l : ℕ, ∃ w : MatrixStage A (l + 1),
      0 ≤ w ∧ ‖w‖ ≤ δ j ∧ ∀ τ : TracialState A,
        0 ≤ (τ.functional (s • (completedSourceU a (j + 1) - completedSourceU a j))).re - (matrixRank τ w).toReal ∧
        (τ.functional (s • (completedSourceU a (j + 1) - completedSourceU a j))).re - (matrixRank τ w).toReal ≤ η j := by
    obtain ⟨l, w, hw, he⟩ := trace_rank_approximation hsimple hinf hT _
      (completedSourceU_increment_nonneg a ha s hs j) (η j) (hη j)
    obtain ⟨v, hv, hn, hr⟩ := exists_small_matrix_same_rank w hw (δ j) (hδ j)
    exact ⟨l, v, hv, hn, fun τ => by rw [hr τ]; exact he τ⟩
  choose l w hw hn he using hex
  refine ⟨l, w, hw, hn, fun j τ => ?_⟩
  simpa only [τ.functional.map_smul_of_tower, map_sub, Complex.smul_re,
    Complex.sub_re, smul_eq_mul, mul_sub] using he j τ
end CuntzPureness

end

end OAI

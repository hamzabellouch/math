import Mathlib.Algebra.BigOperators.Module
import OAI.NumberTheory.Ostmann.QuadraticCenter.RealQuadraticPhase

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

noncomputable def discreteVariation (w : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖w (N - 1)‖ + ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖

/-- Finite Abel summation bounds a weighted sum by the largest prefix sum
and the endpoint-plus-variation of the actual weights. -/
theorem weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ M) :
    ‖∑ j ∈ Finset.range N, w j * f j‖ ≤ discreteVariation w N * M := by
  have hab := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (N - 1) * ∑ j ∈ Finset.range N, f j‖ +
        ‖∑ j ∈ Finset.range (N - 1), (w (j + 1) - w j) * ∑ i ∈ Finset.range (j + 1), f i‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * M +
        ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖ * M := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.norm_mul]
        apply mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have hh := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [discreteVariation, ← Finset.sum_mul]; ring

/-- A large weighted sum therefore supplies a nonempty unweighted prefix.
For a translated interval the same statement applies after reindexing. -/
theorem exists_large_prefix_of_weighted_sum (w f : ℕ → ℂ) (N : ℕ) (R : ℝ)
    (hR : 0 < R)
    (hlarge : discreteVariation w N * R < ‖∑ j ∈ Finset.range N, w j * f j‖) :
    ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ R < ‖∑ j ∈ Finset.range n, f j‖ := by
  by_contra hex
  have hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ R := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simpa only [Finset.range_zero, Finset.sum_empty, norm_zero] using hR.le
    · apply le_of_not_gt
      intro hh
      exact hex ⟨n, Nat.pos_of_ne_zero hn0, hn, hh⟩
  have hb := weighted_sum_le_variation w f N R hprefix
  linarith

end Ostmann

end OAI

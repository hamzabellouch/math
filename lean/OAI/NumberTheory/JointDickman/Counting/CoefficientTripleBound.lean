import OAI.NumberTheory.JointDickman.Counting.CoefficientThreeForm
import OAI.NumberTheory.JointDickman.Amplification.RectangleRemainder

namespace OAI

/-! # Uniform three-form coefficient estimate (manuscript equation (7)) -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Rectangles with both side lengths exponential in B have total
three-coefficient mass bounded by their area times Σ(j). The estimate
is uniform in every positive j and in the position of the rectangle. -/
theorem coefficient_three_form_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ j u v w x : ℕ,
      j ≠ 0 → u ≤ v → w ≤ x →
      Real.exp (δ * B) ≤ (v : ℝ) - u → Real.exp (δ * B) ≤ (x : ℝ) - w →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x,
        coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)) ≤
        C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j := by
  obtain ⟨C, hC, hbound⟩ := coefficient_three_form_with_remainder hFord hM
    (by linarith : 0 < (δ / 8) / 2)
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    coefficient_rectangle_remainder_small hδ, eventually_gt_atTop 1] with B hcut herror hB
  intro j u v w x hj huv hwx hL hH
  have h := hbound B (sieveCutoff (δ / 8) B) j u v w x hB hcut.1 hcut.2.1 hcut.2.2.1 hj huv hwx
  have herr := herror ((v : ℝ) - u) ((x : ℝ) - w) hL hH
  have harea : 0 ≤ ((v : ℝ) - u) * ((x : ℝ) - w) :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast huv)) (sub_nonneg.mpr (by exact_mod_cast hwx))
  calc
    _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        ((v : ℝ) - u) * ((x : ℝ) - w) := h.trans (add_le_add le_rfl herr)
    _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) * singularFactor 24 j +
        (((v : ℝ) - u) * ((x : ℝ) - w)) * singularFactor 24 j :=
      add_le_add le_rfl (le_mul_of_one_le_right harea (singularFactor_one_le (by norm_num) j))
    _ = _ := by ring

end JointDickman

end OAI

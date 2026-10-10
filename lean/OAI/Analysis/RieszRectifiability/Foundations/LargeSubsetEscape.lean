import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NonconcentrationPoint

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_support_point_in_subset_away_from_plane {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ c : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (s : Set (Ambient d)) (hs : s ⊆ ball (0 : Ambient d) R)
    (hmass : c * R ^ n ≤ μ.real s)
    (hsmall : (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ < c) :
    ∃ x ∈ s, x ∈ μ.support ∧ τ * R ≤ infDist x (S : Set (Ambient d)) := by
  have htube : μ.real (affineTube S R (τ * R)) < μ.real s :=
    (lower_dimensional_affineTube_bound μ C hg S hS hkn R τ hR hτ hτ1).trans_lt
      ((mul_lt_mul_of_pos_right hsmall (pow_pos hR n)).trans_le hmass)
  have hfinite : μ (affineTube S R (τ * R)) ≠ ∞ :=
    ne_of_lt ((affineTube_measure_bound μ C hg S hS R (τ * R) hR.le (mul_pos hτ hR)).trans_lt
      ENNReal.ofReal_lt_top)
  obtain ⟨x, hx, hsupport, hout⟩ := exists_support_point_outside_small_set μ s
    (affineTube S R (τ * R)) hfinite htube
  refine ⟨x, hx, hsupport, le_of_not_gt ?_⟩
  intro hnear
  exact hout ⟨ball_subset_closedBall (hs hx), hnear⟩

theorem exists_uniform_affine_escape_width_for_subsets (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → ∀ s : Set (Ambient d), s ⊆ ball (0 : Ambient d) R →
      c * R ^ n ≤ μ.real s →
      ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
        ∃ x ∈ s, x ∈ μ.support ∧ τ * R ≤ infDist x (S : Set (Ambient d)) := by
  let D : ℝ := C * (2 : ℝ) ^ n * (3 : ℝ) ^ n
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  let τ := min 1 (c / (2 * (D + 1)))
  have hden : 0 < 2 * (D + 1) := by positivity
  have hτ : 0 < τ := lt_min zero_lt_one (div_pos hc hden)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτb : τ * (2 * (D + 1)) ≤ c := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : D * τ < c := by nlinarith [mul_nonneg hD hτ.le]
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hg R hR s hs hmass k hkn S hS
  apply exists_support_point_in_subset_away_from_plane μ C hg S hS hkn R τ c hR hτ hτ1
    s hs hmass
  have hK : C * (2 : ℝ) ^ n * (3 : ℝ) ^ k ≤ D := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkn.le)
      (mul_nonneg hC (by positivity))
  exact (mul_le_mul_of_nonneg_right hK hτ.le).trans_lt hsmall

end

end RieszRectifiability

end OAI

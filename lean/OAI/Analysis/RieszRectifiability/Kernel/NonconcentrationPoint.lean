import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.AffineTubeMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_support_point_outside_small_set {d : ℕ}
    (μ : Measure (Ambient d)) (s bad : Set (Ambient d)) (hbad : μ bad ≠ ∞)
    (hlt : μ.real bad < μ.real s) :
    ∃ x ∈ s, x ∈ μ.support ∧ x ∉ bad := by
  by_contra hnone
  have hsub : s ≤ᵐ[μ] bad := by
    filter_upwards [μ.support_mem_ae] with x hx
    intro hxs
    by_contra hxb
    exact hnone ⟨x, hxs, hx, hxb⟩
  have h := ENNReal.toReal_mono hbad (measure_mono_ae hsub)
  exact (not_le_of_gt hlt) h

theorem exists_support_point_away_from_plane {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ c : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (hsmall : (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ < c) :
    ∃ x ∈ ball (0 : Ambient d) R, x ∈ μ.support ∧
      τ * R ≤ infDist x (S : Set (Ambient d)) := by
  have htube : μ.real (affineTube S R (τ * R)) < μ.real (ball (0 : Ambient d) R) :=
    (lower_dimensional_affineTube_bound μ C hg S hS hkn R τ hR hτ hτ1).trans_lt
      ((mul_lt_mul_of_pos_right hsmall (pow_pos hR n)).trans_le hmass)
  have hfinite : μ (affineTube S R (τ * R)) ≠ ∞ :=
    ne_of_lt ((affineTube_measure_bound μ C hg S hS R (τ * R) hR.le (mul_pos hτ hR)).trans_lt
      ENNReal.ofReal_lt_top)
  obtain ⟨x, hx, hsupport, hout⟩ :=
    exists_support_point_outside_small_set μ (ball (0 : Ambient d) R)
      (affineTube S R (τ * R)) hfinite htube
  refine ⟨x, hx, hsupport, ?_⟩
  apply le_of_not_gt
  intro hnear
  exact hout ⟨ball_subset_closedBall hx, hnear⟩

theorem exists_uniform_affine_escape_width {n d : ℕ}
    (μ : Measure (Ambient d)) (C c : ℝ) (hg : GlobalUpperGrowth n C μ) (hc : 0 < c)
    (R : ℝ) (hR : 0 < R) (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
        ∃ x ∈ ball (0 : Ambient d) R, x ∈ μ.support ∧
          τ * R ≤ infDist x (S : Set (Ambient d)) := by
  let D : ℝ := C * (2 : ℝ) ^ n * (3 : ℝ) ^ n
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hg.1 (by positivity)) (by positivity)
  let τ := min 1 (c / (2 * (D + 1)))
  have hden : 0 < 2 * (D + 1) := by positivity
  have hτ : 0 < τ := lt_min zero_lt_one (div_pos hc hden)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτb : τ * (2 * (D + 1)) ≤ c := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : D * τ < c := by nlinarith [mul_nonneg hD hτ.le]
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro k hkn S hS
  apply exists_support_point_away_from_plane μ C hg S hS hkn R τ c hR hτ hτ1 hmass
  have hK : C * (2 : ℝ) ^ n * (3 : ℝ) ^ k ≤ D := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkn.le)
      (mul_nonneg hg.1 (by positivity))
  exact (mul_le_mul_of_nonneg_right hK hτ.le).trans_lt hsmall

end

end RieszRectifiability

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.MeasuredPlaneComparison
import OAI.Analysis.RieszRectifiability.Nets.ScaleAnchorConditioning

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_measured_plane_comparison (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η → η ≤ ε * R →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∀ x ∈ S, infDist x (W : Set (Ambient d)) ≤ A * η * (1 + ‖x‖ / R) := by
  obtain ⟨τ, hτ, _hτ1, hcompare⟩ := exists_measured_plane_comparison_width n d C c hC hc
  let K := spanConditionConstant 2 τ n
  have hK : 0 ≤ K := spanConditionConstant_nonneg 2 τ (by norm_num) hτ n
  let ε := min 1 (1 / (4 * (K + 1)))
  have hden : 0 < 4 * (K + 1) := by positivity
  have hε : 0 < ε := lt_min zero_lt_one (div_pos zero_lt_one hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεb : ε * (4 * (K + 1)) ≤ 1 := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmallK : K * (2 * ε) ≤ 1 / 2 := by nlinarith
  let A := 2 * (1 + 8 * K)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, ε, hA, hε, hε1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr x hx
  have hscale : spanConditionConstant (2 * R) (τ * R) n = K / R :=
    spanConditionConstant_rescale 2 τ R hτ.ne' hR.ne' n
  have hratio : η / R ≤ ε := (div_le_iff₀ hR).mpr hηsmall
  have hsmall : spanConditionConstant (2 * R) (τ * R) n * (2 * η) ≤ 1 / 2 := by
    rw [hscale]
    calc
      (K / R) * (2 * η) = K * (2 * (η / R)) := by ring
      _ ≤ K * (2 * ε) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)) hK
      _ ≤ 1 / 2 := hsmallK
  obtain ⟨a, _ha, hanorm, hcomp⟩ := hcompare μ hfinite hg R hR hmass S W hS hW η hη herr hsmall
  have hηR : η ≤ R := hηsmall.trans
    ((mul_le_mul_of_nonneg_right hε1 hR.le).trans_eq (one_mul R))
  have hxa : ‖x - a‖ ≤ ‖x‖ + 2 * R := (norm_sub_le x a).trans (by linarith)
  have hn : ‖x - a‖ / R ≤ ‖x‖ / R + 2 := by
    apply (div_le_iff₀ hR).mpr
    calc
      ‖x - a‖ ≤ ‖x‖ + 2 * R := hxa
      _ = (‖x‖ / R + 2) * R := by field_simp
  have hq : 0 ≤ ‖x‖ / R := div_nonneg (norm_nonneg x) hR.le
  have hfactor : 1 + 4 * K * (‖x‖ / R + 2) ≤ (1 + 8 * K) * (1 + ‖x‖ / R) := by
    nlinarith [mul_nonneg hK hq]
  calc
    infDist x (W : Set (Ambient d)) ≤
        2 * η * (1 + 4 * spanConditionConstant (2 * R) (τ * R) n * ‖x - a‖) := hcomp x hx
    _ = 2 * η * (1 + 4 * K * (‖x - a‖ / R)) := by rw [hscale]; ring
    _ ≤ 2 * η * (1 + 4 * K * (‖x‖ / R + 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 4 * K))) (by positivity)
    _ ≤ 2 * η * ((1 + 8 * K) * (1 + ‖x‖ / R)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = A * η * (1 + ‖x‖ / R) := by dsimp only [A]; ring

end

end RieszRectifiability

end OAI

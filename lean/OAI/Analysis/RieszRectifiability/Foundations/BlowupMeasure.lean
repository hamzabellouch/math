import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure

namespace OAI

/-!
# Rescaled measures and their growth bounds

The blowup at a center and positive scale pushes a measure forward by translation
and dilation, then normalizes by the scale to the power `n`. Exact ball formulas
transport the support and preserve global upper and lower growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def blowupMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) : Measure (Ambient d) :=
  ENNReal.ofReal ((r ^ n)⁻¹) • μ.map (fun y => r⁻¹ • (y - a))

theorem blowup_preimage_ball {d : ℕ} (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' ball x R = ball (a + r • x) (r * R) := by
  ext y
  have hvec : y - (a + r • x) = r • (r⁻¹ • (y - a) - x) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hdist : dist y (a + r • x) = r * dist (r⁻¹ • (y - a)) x := by
    simp only [dist_eq_norm]
    rw [hvec, norm_smul, Real.norm_of_nonneg hr.le]
  simp only [mem_preimage, mem_ball, hdist]
  exact (mul_lt_mul_iff_right₀ hr).symm

theorem blowupMeasure_ball {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    blowupMeasure n μ a r (ball x R) =
      ENNReal.ofReal ((r ^ n)⁻¹) * μ (ball (a + r • x) (r * R)) := by
  have hblowup : Measurable (fun y : Ambient d => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  rw [blowupMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hblowup measurableSet_ball, blowup_preimage_ball a x r R hr]

theorem blowupMeasure_growth {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r) (hg : GlobalUpperGrowth n C μ) :
    GlobalUpperGrowth n C (blowupMeasure n μ a r) := by
  refine ⟨hg.1, ?_⟩
  intro x R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  calc
    _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal (C * (r * R) ^ n) :=
      mul_le_mul_right (hg.2 (a + r • x) (r * R) (by positivity)) _
    _ = ENNReal.ofReal (C * R ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp

theorem blowupMeasure_support_iff {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r : ℝ) (hr : 0 < r) :
    x ∈ (blowupMeasure n μ a r).support ↔ a + r • x ∈ μ.support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  have hcoef : 0 < ENNReal.ofReal ((r ^ n)⁻¹) := ENNReal.ofReal_pos.mpr (by positivity)
  constructor
  · intro hx R hR
    have h := hx (R / r) (by positivity)
    rw [blowupMeasure_ball n μ a x r (R / r) hr,
      mul_div_cancel₀ R hr.ne'] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx R hR
    rw [blowupMeasure_ball n μ a x r R hr]
    exact ENNReal.mul_pos_iff.mpr ⟨hcoef, hx (r * R) (by positivity)⟩

theorem blowupMeasure_origin_mem_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (ha : a ∈ μ.support) :
    (0 : Ambient d) ∈ (blowupMeasure n μ a r).support := by
  apply (blowupMeasure_support_iff n μ a 0 r hr).mpr
  simpa only [smul_zero, add_zero] using! ha

theorem blowupMeasure_lower_global {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R)) :
    ∀ x ∈ (blowupMeasure n μ a r).support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ blowupMeasure n μ a r (ball x R) := by
  intro x hx R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  have h := hlower (a + r • x) ((blowupMeasure_support_iff n μ a x r hr).mp hx)
    (r * R) (by positivity)
  calc
    _ = ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal ((r * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right h _

end

end RieszRectifiability

end OAI

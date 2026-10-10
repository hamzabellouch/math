import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TailBounds
import OAI.Analysis.RieszRectifiability.Kernel.FarKernelDifference

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_radial_bound {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a y : Ambient d) (R : ℝ)
    (hR : 0 < R) (hy : R ≤ dist a y) :
    |w y| ≤ ((K : ℝ) + |w a| / R) * dist a y := by
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have hconstant : |w a| ≤ (|w a| / R) * dist a y := by
    have h := mul_le_mul_of_nonneg_left hy (div_nonneg (abs_nonneg (w a)) hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using! h
  calc
    _ ≤ |w y - w a| + |w a| := by
      simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
    _ ≤ (K : ℝ) * dist a y + (|w a| / R) * dist a y := add_le_add hdiff hconstant
    _ = _ := by ring

theorem cancelled_height_far_bound {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a x y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| ≤
      (((K : ℝ) + |w a| / R) * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) *
        inverseDistancePow (m + 1) a y := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hdiff := inverseDistancePow_far_difference m a x y hpos (hx.trans hy)
  rw [abs_mul]
  calc
    _ ≤ (((K : ℝ) + |w a| / R) * dist a y) *
        ((m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y) :=
      mul_le_mul (lipschitz_height_radial_bound w K hw a y R hR hy) hdiff (abs_nonneg _)
        (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      field_simp
      ring

theorem cancelled_height_tail_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) :
    IntegrableOn (fun y => w y *
      (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
      {y | R < dist a y} μ ∧
      (∫ y in {y | R < dist a y}, |w y *
        (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| ∂μ) ≤
        (((K : ℝ) + |w a| / R) * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) *
          (2 * (C * 2 ^ m / R)) := by
  let B := ((K : ℝ) + |w a| / R) * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hweight := inverseDistancePow_integrableOn_exterior m C μ hg a R hR
  have hs : MeasurableSet {y | R < dist a y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have hm : Measurable (fun y => w y *
      (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)) :=
    hw.continuous.measurable.mul
      ((inverseDistancePow_measurable _ _).sub (inverseDistancePow_measurable _ _))
  have hi : IntegrableOn (fun y => w y *
      (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
      {y | R < dist a y} μ := by
    apply (hweight.const_mul B).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with y hy
    simpa only [Real.norm_eq_abs] using! cancelled_height_far_bound m w K hw a x y R hR hx hy.le
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in {y | R < dist a y}, B * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi.abs (hweight.const_mul B)
      filter_upwards [ae_restrict_mem hs] with y hy
      exact cancelled_height_far_bound m w K hw a x y R hR hx hy.le
    _ = B * (∫ y in {y | R < dist a y}, inverseDistancePow (m + 1) a y ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (inverseDistancePow_exterior_integral_bound m C μ hg a R hR) hB

end

end RieszRectifiability

end OAI

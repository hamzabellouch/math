import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def GlobalUpperGrowth {d : ℕ} (n : ℕ) (C : ℝ) (μ : Measure (Ambient d)) : Prop :=
  0 ≤ C ∧ ∀ x : Ambient d, ∀ r : ℝ, 0 < r →
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

theorem kernel_norm_le_truncation {d : ℕ} (n : ℕ) (x y : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ≤ (ε ^ n)⁻¹ := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd)]
  simpa only [one_div] using!
    one_div_le_one_div_of_le (pow_pos hε n) (pow_le_pow_left₀ hε.le hy n)

def inverseDistancePow {d : ℕ} (p : ℕ) (x y : Ambient d) : ℝ :=
  (dist x y ^ p)⁻¹

theorem inverseDistancePow_measurable {d : ℕ} (p : ℕ) (x : Ambient d) :
    Measurable (inverseDistancePow p x) := by
  unfold inverseDistancePow
  fun_prop

theorem inverseDistancePow_nonneg {d : ℕ} (p : ℕ) (x y : Ambient d) :
    0 ≤ inverseDistancePow p x y := by
  unfold inverseDistancePow
  positivity

end

end RieszRectifiability

end OAI

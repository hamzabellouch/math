import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityDerivative
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-!
# Partial summation for the local prime-product law

Harmonic weighting of a counting estimate costs only the logarithmic
length of the interval. The finite counting function is kept explicit.
-/

namespace JointDickman

open Finset MeasureTheory
open scoped Interval

noncomputable def finiteCountingFunction (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊t⌋₊, w n

theorem sum_div_eq_boundary_add_integral (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) =
      finiteCountingFunction w b / b - finiteCountingFunction w a / a +
        ∫ t in a..b, finiteCountingFunction w t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    simp only [deriv_inv']
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul (c := w) ha.le hab hd hi
  rw [← intervalIntegral.integral_of_le hab] at h
  simp only [deriv_inv] at h
  have heq : (fun t : ℝ => -(t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, w n) =
      (fun t => -(finiteCountingFunction w t / t ^ 2)) := by
    funext t
    unfold finiteCountingFunction
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  simpa only [div_eq_mul_inv, mul_comm, finiteCountingFunction, sub_neg_eq_add] using h

theorem finiteCountingFunction_div_sq_integrable (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => finiteCountingFunction w t / t ^ 2) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
  have hi := integrableOn_mul_sum_Icc (m := 0) w ha.le hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [finiteCountingFunction, div_eq_mul_inv, mul_comm] using hi

/-- The integrated counting error is controlled by the logarithmic length. -/
theorem integral_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| ≤ ε * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hmajor : IntervalIntegrable (fun t => ε / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le (Set.uIcc_of_le hab ▸ ht).1)
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun t => (finiteCountingFunction w t - F t) / t ^ 2)
    (g := fun t => ε / t) (Filter.Eventually.of_forall (fun t ht => ?_)) hmajor
  · simpa only [Real.norm_eq_abs, div_eq_mul_inv, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha hb] using h
  have ht0 : 0 < t := ha.trans_le ht.1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
  calc
    _ ≤ ε * t / t ^ 2 := div_le_div_of_nonneg_right (herr t ⟨ht.1.le, ht.2⟩) (sq_nonneg t)
    _ = ε / t := by field_simp

/-- Harmonic weighting loses at most two endpoint errors and one logarithm. -/
theorem harmonic_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2)| ≤
        ε * (2 + Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hF.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hGi := finiteCountingFunction_div_sq_integrable w ha hab
  have hint : (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (∫ t in a..b, F t / t ^ 2) =
      ∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hGi hFi]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      |(finiteCountingFunction w t - F t) / t| ≤ ε := by
    have ht0 : 0 < t := ha.trans_le ht.1
    rw [abs_div, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr (herr t ht)
  rw [sum_div_eq_boundary_add_integral w ha hab]
  have heq : finiteCountingFunction w b / b - finiteCountingFunction w a / a +
      (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2) =
      ((finiteCountingFunction w b - F b) / b - (finiteCountingFunction w a - F a) / a) +
        ((∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
          (∫ t in a..b, F t / t ^ 2)) := by ring
  rw [heq, hint]
  calc
    _ ≤ |(finiteCountingFunction w b - F b) / b| + |(finiteCountingFunction w a - F a) / a| +
        |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ ε + ε + ε * Real.log (b / a) :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩))
        (integral_counting_error_le w F ha hab herr)
    _ = _ := by ring

/-- Integration of the model's derivative gives the same harmonic model. -/
theorem harmonic_model_integral (F M : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (M t) t)
    (hM : ContinuousOn M (Set.Icc a b)) :
    (∫ t in a..b, M t / t) = F b / b - F a / a + ∫ t in a..b, F t / t ^ 2 := by
  have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hMi : IntervalIntegrable (fun t => M t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hM.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hFc.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => F x / x) (M t / t - F t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    convert (hF t ht).div (hasDerivAt_id t) ht0 using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hMi.sub hFi)
  rw [intervalIntegral.integral_sub hMi hFi] at h
  linarith

end JointDickman

end OAI

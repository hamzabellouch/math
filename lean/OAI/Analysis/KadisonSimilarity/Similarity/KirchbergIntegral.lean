import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergNumerics
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! The fundamental-theorem-of-calculus estimate in Kirchberg's
Proposition 1, page 61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace MeasureTheory Set
open scoped Topology

theorem integral_const_rpow_unit {K : ℝ} (hK : 1 < K) :
    (∫ s : ℝ in 0..1, K ^ s) = (K - 1) / Real.log K := by
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hl : Real.log K ≠ 0 := ne_of_gt (Real.log_pos hK)
  have hder (s : ℝ) : HasDerivAt (fun x : ℝ => K ^ x / Real.log K) (K ^ s) s := by
    simpa only [mul_div_cancel_right₀ _ hl] using
      (Real.hasStrictDerivAt_const_rpow hK0 s).hasDerivAt.div_const (Real.log K)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hder s) ((Real.continuous_const_rpow hK0.ne').intervalIntegrable 0 1)
  simpa only [Real.rpow_one, Real.rpow_zero, ← sub_div] using h

section Algebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

local instance kirchbergIntegralRatAlgebra : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B

theorem real_conjugation_hasDerivAt (t a : B) (s : ℝ) :
    HasDerivAt (fun x : ℝ => exp (x • (-t)) * a * exp (x • t))
      (exp (s • (-t)) * (a * t - t * a) * exp (s • t)) s := by
  have h := ((hasDerivAt_exp_smul_const (-t) s).mul_const a).mul
    (hasDerivAt_exp_smul_const t s)
  have hc : Commute t (exp (s • t)) := ((Commute.refl t).smul_right s).exp_right
  convert h using 1
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, ← hc.eq]
  abel

theorem real_conjugation_integral (t a : B) :
    (∫ s : ℝ in 0..1, exp (s • (-t)) * (a * t - t * a) * exp (s • t)) =
      exp (-t) * a * exp t - a := by
  have hc : Continuous (fun s : ℝ => exp (s • (-t)) * (a * t - t * a) * exp (s • t)) := by
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => real_conjugation_hasDerivAt t a s) (hc.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] using h

/-- The matrix-independent path estimate. The precise condition-number
scaling is supplied separately by functional calculus. -/
theorem norm_real_conjugation_le (t a : B) {K : ℝ} (hK : 1 < K)
    (hscale : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖exp (s • (-t))‖ * ‖exp (s • t)‖ ≤ K ^ s) :
    ‖exp (-t) * a * exp t‖ ≤
      ‖a‖ + ‖a * t - t * a‖ * ((K - 1) / Real.log K) := by
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hint : IntervalIntegrable (fun s : ℝ => ‖a * t - t * a‖ * K ^ s) volume 0 1 :=
    (continuous_const.mul (Real.continuous_const_rpow hK0.ne')).intervalIntegrable 0 1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => exp (s • (-t)) * (a * t - t * a) * exp (s • t)) zero_le_one
    (Filter.Eventually.of_forall (fun s hs => show
      ‖exp (s • (-t)) * (a * t - t * a) * exp (s • t)‖ ≤
        ‖a * t - t * a‖ * K ^ s from by
      calc
        _ ≤ (‖exp (s • (-t))‖ * ‖a * t - t * a‖) * ‖exp (s • t)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖a * t - t * a‖ * (‖exp (s • (-t))‖ * ‖exp (s • t)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale s hs) (norm_nonneg _))) hint
  rw [real_conjugation_integral, intervalIntegral.integral_const_mul,
    integral_const_rpow_unit hK] at hbound
  calc
    _ = ‖a + (exp (-t) * a * exp t - a)‖ := by congr 1; abel
    _ ≤ ‖a‖ + ‖exp (-t) * a * exp t - a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hbound

end Algebra
end KadisonSimilarity

end

end OAI

import OAI.NumberTheory.Ostmann.Preliminaries.MertensThetaKernel
import OAI.NumberTheory.Ostmann.Preliminaries.MertensFromFirst

namespace OAI

/-! # Mertens estimates from the progression estimate

The conductor-one theta bound implies the first Mertens estimate.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

/-- Abel summation for the logarithmically weighted prime sum. -/
theorem prime_log_div_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) =
      Chebyshev.theta Q / Q + ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : ContinuousOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 2 Q) := by
    simp only [deriv_inv']
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have h := sum_mul_eq_sub_integral_mul₁ (primeProgressionLog 1 0)
    (by norm_num [primeProgressionLog]) (by norm_num [primeProgressionLog]) (Q : ℝ)
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt)
    hd.integrableOn_Icc
  have hs : (∑ n ∈ Icc 0 Q, (n : ℝ)⁻¹ * primeProgressionLog 1 0 n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n hn
    simp [primeProgressionLog, Nat.ModEq, Nat.mod_one, mul_ite, div_eq_mul_inv, mul_comm]
  change _ = (Q : ℝ)⁻¹ * primeProgressionTheta 1 0 Q -
    ∫ t in Set.Ioc (2 : ℝ) Q, deriv (fun t : ℝ => t⁻¹) t *
      primeProgressionTheta 1 0 t at h
  rw [Nat.floor_natCast, hs] at h
  simp_rw [primeProgressionTheta_one, deriv_inv, neg_mul] at h
  rw [← intervalIntegral.integral_of_le hQR, intervalIntegral.integral_neg,
    sub_neg_eq_add] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

private theorem theta_div_sq_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 2 Q) := by
    exact (continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have h := integrableOn_mul_sum_Icc (primeProgressionLog 1 0)
    (m := 0) (show (0 : ℝ) ≤ 2 by norm_num) hc.integrableOn_Icc
  change IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * primeProgressionTheta 1 0 t)
    (Set.Icc 2 Q) at h
  simpa only [primeProgressionTheta_one, div_eq_mul_inv, mul_comm] using h

/-- The integrated theta error is bounded independently of the cutoff. -/
theorem PublishedProgressionInput.theta_error_integral (P : PublishedProgressionInput)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2| ≤
      P.errorConstant * (-thetaErrorPrimitive P.decay 2) := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hk : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  have hi : IntervalIntegrable (fun t : ℝ =>
      (Chebyshev.theta t - t) / t ^ 2) volume 2 Q := by
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    apply ((theta_div_sq_integrable Q hQ).sub hv).congr
    intro t ht
    rw [Set.uIoc_of_le hQR] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q, |(Chebyshev.theta t - t) / t ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR
          (f := fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2))
    _ ≤ ∫ t in (2 : ℝ)..Q,
        P.errorConstant * (Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) := by
      apply intervalIntegral.integral_mono_on hQR hi.norm (hk.const_mul _)
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      calc
        _ ≤ (P.errorConstant * t * Real.exp (-P.decay * Real.sqrt (Real.log t))) /
            t ^ 2 := div_le_div_of_nonneg_right (P.principal_theta_bound t ht.1)
              (sq_nonneg _)
        _ = _ := by field_simp
    _ = P.errorConstant * ∫ t in (2 : ℝ)..Q,
        Real.exp (-P.decay * Real.sqrt (Real.log t)) / t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (theta_error_kernel_integral_bound P.decay_pos hQR) P.errorConstant_nonneg

noncomputable def PublishedProgressionInput.mertensConstant (P : PublishedProgressionInput) : ℝ :=
  |1 - Real.log 2| + P.errorConstant +
    P.errorConstant * (-thetaErrorPrimitive P.decay 2)

theorem PublishedProgressionInput.mertensConstant_nonneg (P : PublishedProgressionInput) :
    0 ≤ P.mertensConstant := by
  unfold PublishedProgressionInput.mertensConstant
  exact add_nonneg (add_nonneg (abs_nonneg _) P.errorConstant_nonneg)
    (mul_nonneg P.errorConstant_nonneg (neg_nonneg.mpr
      (thetaErrorPrimitive_nonpos P.decay_pos 2)))

/-- First Mertens, with a concrete constant depending on the
progression estimate. -/
theorem PublishedProgressionInput.mertens (P : PublishedProgressionInput) :
    MertensEstimate P.mertensConstant := by
  intro Q hQ
  by_cases hQ2 : 2 ≤ Q
  · have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    have hQ0 : (0 : ℝ) < Q := by linarith
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    have hsplit : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
        (∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2) -
          (Real.log Q - Real.log 2) := by
      have he : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
          ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 - t⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hQR] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
      rw [he, intervalIntegral.integral_sub (theta_div_sq_integrable Q hQ2) hv,
        integral_inv_of_pos (by norm_num) hQ0,
        Real.log_div hQ0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hid : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q =
        (1 - Real.log 2) + (Chebyshev.theta Q - Q) / Q +
          ∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2 := by
      rw [hsplit, prime_log_div_partial_summation Q hQ2]
      field_simp
      ring
    have hend : |(Chebyshev.theta Q - Q) / Q| ≤ P.errorConstant := by
      rw [abs_div, abs_of_pos hQ0]
      calc
        _ ≤ (P.errorConstant * Q * Real.exp (-P.decay * Real.sqrt (Real.log Q))) / Q :=
          div_le_div_of_nonneg_right (P.principal_theta_bound Q hQR) hQ0.le
        _ = P.errorConstant * Real.exp (-P.decay * Real.sqrt (Real.log Q)) := by
          field_simp
        _ ≤ P.errorConstant * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr P.decay_pos.le) (Real.sqrt_nonneg _))) P.errorConstant_nonneg
        _ = _ := mul_one _
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add le_rfl hend) (P.theta_error_integral Q hQ2))
  · have hQ1 : Q = 1 := by omega
    subst Q
    simpa only [Nat.primesLE_one, sum_empty, Nat.cast_one, Real.log_one, sub_self,
      abs_zero] using P.mertensConstant_nonneg

end Ostmann

end OAI

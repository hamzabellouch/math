import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrincipalMean
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrimePowerRemoval

namespace OAI

/-! # The fixed principal-character mean by partial summation

This identifies the literal smooth mean with a compactly supported integral
of the Chebyshev function, for use with the quantitative PNT.
-/

namespace Ostmann

open MeasureTheory Finset
open scoped Classical BigOperators Interval

theorem primeMeanTest_deriv_continuous : Continuous (deriv primeMeanTest) :=
  (primeMeanTest_contDiff (n := 1)).continuous_deriv_one

theorem primeMeanTest_deriv_zero_outside (t : ℝ)
    (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) : deriv primeMeanTest t = 0 := by
  have hs : tsupport primeMeanTest ⊆ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    exact hx (primeMeanTest_zero_outside x hn)
  exact deriv_of_notMem_tsupport (fun h => ht (hs h))

theorem primeMeanTest_deriv_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, |deriv primeMeanTest t| ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    primeMeanTest_deriv_continuous.continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8)
  · have h := hD t ht
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self D]
  · rw [primeMeanTest_deriv_zero_outside t ht, abs_zero]
    positivity

theorem scaledPrimeMeanTest_hasDerivAt (X t : ℝ) :
    HasDerivAt (fun s : ℝ => primeMeanTest (s / X))
      (deriv primeMeanTest (t / X) / X) t := by
  have h := (((primeMeanTest_contDiff (n := 1)).differentiable
      (by norm_num)) (t / X)).hasDerivAt |>.comp t ((hasDerivAt_id t).div_const X)
  simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using h

theorem smoothPrincipalMean_eq_real_sum (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean 1 1 X =
      ((∑ n ∈ Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n *
        primeMeanTest (n / X) : ℝ) : ℂ) := by
  rw [smoothMangoldtMean_eq_sum 1 1 X hX]
  have heq : (∑ n ∈ Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n *
      primeMeanTest (n / X)) =
      ∑ n ∈ Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * primeMeanTest (n / X) := by
    rw [← sum_Ioc_add_eq_sum_Icc (Nat.zero_le ⌊X⌋₊)]
    simp
  rw [← heq]
  push_cast
  apply sum_congr rfl
  intro n hn
  have hn1 : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hn1]
  simp

theorem smoothPrincipalMean_partial_summation (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean 1 1 X =
      ((-(∫ t in (0 : ℝ)..X,
        deriv primeMeanTest (t / X) / X * Chebyshev.psi t) : ℝ) : ℂ) := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  have hd : deriv (fun t : ℝ => primeMeanTest (t / X)) =
      fun t : ℝ => deriv primeMeanTest (t / X) / X := by
    funext t
    exact (scaledPrimeMeanTest_hasDerivAt X t).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => primeMeanTest (t / X)))
      (Set.Icc 0 X) := by rw [hd]; exact hf.continuousOn.integrableOn_Icc
  have hs := sum_mul_eq_sub_integral_mul ArithmeticFunction.vonMangoldt hX.le
    (f := fun t : ℝ => primeMeanTest (t / X))
    (fun t _ => (scaledPrimeMeanTest_hasDerivAt X t).differentiableAt) hi
  rw [hd] at hs
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hs
  rw [show primeMeanTest (X / X) = 0 by
    rw [div_self hX.ne']; exact primeMeanTest_zero_outside 1 (by norm_num), zero_mul,
    zero_sub, ← intervalIntegral.integral_of_le hX.le] at hs
  rw [smoothPrincipalMean_eq_real_sum X hX]
  congr 1
  simpa only [mul_comm] using hs

theorem primeMeanTest_integral_unit :
    (∫ t in (0 : ℝ)..1, primeMeanTest t) = ∫ t : ℝ, primeMeanTest t := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hmem : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    by_contra hn
    exact ht (primeMeanTest_zero_outside t hn)
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem scaledPrimeMean_main_integral (X : ℝ) (hX : 0 < X) :
    (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X * t) =
      -(X * ∫ t : ℝ, primeMeanTest t) := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ : ℝ => 1)
    (v := fun t : ℝ => primeMeanTest (t / X))
    (v' := fun t : ℝ => deriv primeMeanTest (t / X) / X)
    (fun t _ => hasDerivAt_id t) (fun t _ => scaledPrimeMeanTest_hasDerivAt X t)
    (intervalIntegrable_const) (hf.intervalIntegrable 0 X)
  have hzero : primeMeanTest (X / X) = 0 := by
    rw [div_self hX.ne']
    exact primeMeanTest_zero_outside 1 (by norm_num)
  simp only [hzero, one_mul, zero_mul, mul_zero, sub_zero, zero_sub] at hs
  rw [intervalIntegral.integral_comp_div primeMeanTest hX.ne'] at hs
  simpa only [mul_comm, zero_div, div_self hX.ne', smul_eq_mul,
    primeMeanTest_integral_unit] using hs

private theorem scaledPrimeMean_psi_integrable (X : ℝ) (hX : 0 < X) :
    IntervalIntegrable (fun t : ℝ => deriv primeMeanTest (t / X) / X *
      Chebyshev.psi t) volume 0 X := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX.le]
  simpa only [Chebyshev.psi_eq_sum_Icc] using
    (integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0)
      (show (0 : ℝ) ≤ 0 by rfl) hf.continuousOn.integrableOn_Icc)

/-- The exact principal error is the integral of the unsmoothed PNT error. -/
theorem smoothPrincipalError_integral (X : ℝ) (hX : 0 < X) :
    smoothPrincipalError X =
      |∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X *
        (Chebyshev.psi t - t)| := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X * t) :=
    ((primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X).mul
      continuous_id
  have hi : (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X *
      (Chebyshev.psi t - t)) =
      (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X * Chebyshev.psi t) +
        X * ∫ t : ℝ, primeMeanTest t := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (scaledPrimeMean_psi_integrable X hX)
      (hf.intervalIntegrable 0 X), scaledPrimeMean_main_integral X hX, sub_neg_eq_add]
  rw [smoothPrincipalError, smoothPrincipalMean_partial_summation X hX,
    smoothPrincipalMain, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hi]
  rw [Real.norm_eq_abs, sub_eq_add_neg, ← neg_add, abs_neg]

end Ostmann

end OAI

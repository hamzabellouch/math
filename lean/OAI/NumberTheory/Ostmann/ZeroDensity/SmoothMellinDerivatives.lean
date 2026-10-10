import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OAI.NumberTheory.Ostmann.Construction.SmoothPrimeMeanTest

namespace OAI

namespace Ostmann

open MeasureTheory
open scoped BigOperators Interval

theorem primeMeanTest_iteratedDeriv_continuous (n : ℕ) :
    Continuous (iteratedDeriv n primeMeanTest) :=
  (primeMeanTest_contDiff (n := (n : ℕ∞))).continuous_iteratedDeriv' n

theorem primeMeanTest_iteratedDeriv_zero_outside (n : ℕ) (t : ℝ)
    (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) : iteratedDeriv n primeMeanTest t = 0 := by
  induction n generalizing t with
  | zero => simpa using primeMeanTest_zero_outside t ht
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hs : tsupport (iteratedDeriv n primeMeanTest) ⊆
        Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra hn
      exact hx (ih x hn)
    exact deriv_of_notMem_tsupport (fun h => ht (hs h))

theorem primeMeanTest_iteratedDeriv_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, |iteratedDeriv n primeMeanTest t| ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (primeMeanTest_iteratedDeriv_continuous n).continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8)
  · have h := hD t ht
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self D]
  · rw [primeMeanTest_iteratedDeriv_zero_outside n t ht, abs_zero]
    positivity

theorem exp_log_shift (z : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (z * (Real.log t : ℂ)) =
      (t : ℂ) * Complex.exp ((z - 1) * (Real.log t : ℂ)) := by
  have he : z * (Real.log t : ℂ) = (Real.log t : ℂ) +
      (z - 1) * (Real.log t : ℂ) := by ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht]

theorem hasDerivAt_exp_log (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * (Real.log t : ℂ)))
      (z * Complex.exp ((z - 1) * (Real.log t : ℂ))) t := by
  have h := (((Real.hasDerivAt_log ht.ne').ofReal_comp).const_mul z).cexp
  convert h using 1
  rw [exp_log_shift z ht, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

noncomputable def shiftedPrimeMeanMellin (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 / 2 : ℝ)..1,
    ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
      Complex.exp ((s + n - 1) * (Real.log t : ℂ))

theorem shiftedPrimeMeanMellin_zero (s : ℂ) :
    shiftedPrimeMeanMellin 0 s = primeMeanMellin s := by
  simp only [shiftedPrimeMeanMellin, iteratedDeriv_zero, Nat.cast_zero, add_zero,
    primeMeanMellin]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply intervalIntegral.integral_eq_integral_of_support_subset
    intro t ht
    have hmem : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      by_contra hn
      exact ht (by simp only [primeMeanTest_zero_outside t hn, Complex.ofReal_zero, zero_mul])
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  · intro t ht
    rw [primeMeanTest_zero_outside t (by
      intro hm
      exact ht (by linarith [hm.1] : 0 < t)), Complex.ofReal_zero, zero_mul]

theorem shiftedPrimeMeanMellin_succ (n : ℕ) (s : ℂ) :
    shiftedPrimeMeanMellin (n + 1) s = -(s + n) * shiftedPrimeMeanMellin n s := by
  have hu (t : ℝ) : HasDerivAt (fun x : ℝ => ((iteratedDeriv n primeMeanTest x : ℝ) : ℂ))
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ) t := by
    have hd := (primeMeanTest_contDiff (n := ((n + 1 : ℕ) : ℕ∞))).differentiable_iteratedDeriv' n
    have h := (hd t).hasDerivAt.ofReal_comp
    simpa only [iteratedDeriv_succ] using h
  have hv (t : ℝ) (ht : t ∈ Set.uIcc (1 / 2 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => Complex.exp ((s + n) * (Real.log x : ℂ)))
        ((s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ))) t :=
    hasDerivAt_exp_log _ (by rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1])
  have hui : IntervalIntegrable (fun t : ℝ =>
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ)) volume (1 / 2) 1 :=
    (Complex.continuous_ofReal.comp (primeMeanTest_iteratedDeriv_continuous _)).intervalIntegrable _ _
  have hvi : IntervalIntegrable (fun t : ℝ =>
      (s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ))) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    fun_prop (disch := grind)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hu t) hv hui hvi
  have hleft : (∫ t in (1 / 2 : ℝ)..1,
      ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
        ((s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ)))) =
      (s + n) * shiftedPrimeMeanMellin n s := by
    rw [shiftedPrimeMeanMellin, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hleft, primeMeanTest_iteratedDeriv_zero_outside n 1 (by norm_num),
    primeMeanTest_iteratedDeriv_zero_outside n (1 / 2) (by norm_num),
    Complex.ofReal_zero] at hi
  simp only [zero_mul, sub_self, zero_sub] at hi
  have hr : (∫ t in (1 / 2 : ℝ)..1,
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ) *
        Complex.exp ((s + n) * (Real.log t : ℂ))) = shiftedPrimeMeanMellin (n + 1) s := by
    simp only [shiftedPrimeMeanMellin, Nat.cast_add, Nat.cast_one, ← add_assoc, add_sub_cancel_right]
  rw [hr] at hi
  linear_combination hi

end Ostmann

end OAI

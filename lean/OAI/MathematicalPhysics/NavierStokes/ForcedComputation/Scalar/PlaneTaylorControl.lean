import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

namespace OAI

/-! A three-point estimate converting bounded third derivatives and scalar tail
decay into square integrable second derivatives. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open Set
open scoped ContDiff

theorem taylor_two_remainder_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {M s : ℝ} (hs : s ≠ 0) (hM : ∀ t, |iteratedDeriv 3 f t| ≤ M) :
    |f s - (f 0 + s * iteratedDeriv 1 f 0 + (s ^ 2 / 2) * iteratedDeriv 2 f 0)| ≤
      M * |s| ^ 3 / 6 := by
  have hne : (0 : ℝ) ≠ s := Ne.symm hs
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by simp)
  obtain ⟨ξ, _, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hne hf3.contDiffOn
  have hd (k : ℕ) : iteratedDerivWithin k f (uIcc 0 s) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((hf.of_le (by simp)).contDiffAt) left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc 0 s) 0 s =
      f 0 + s * iteratedDeriv 1 f 0 + (s ^ 2 / 2) * iteratedDeriv 2 f 0 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0]
    simp only [taylor_within_zero_eval, hd, sub_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_zero, Nat.cast_one, zero_add, mul_one,
      inv_one, pow_one, smul_eq_mul]
    ring
  rw [hp] at he
  rw [he]
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_one,
    sub_zero, abs_div, abs_mul, abs_pow]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM ξ) (pow_nonneg (abs_nonneg s) 3)) (by norm_num)

theorem second_derivative_three_point_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {M B h : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hthird : ∀ t, |iteratedDeriv 3 f t| ≤ M)
    (hzero : |f 0| ≤ B) (hplus : |f h| ≤ B) (hminus : |f (-h)| ≤ B) :
    |iteratedDeriv 2 f 0| * h ^ 2 ≤ 4 * B + M * h ^ 3 := by
  have hp := taylor_two_remainder_bound hf hh.ne' hthird
  have hm := taylor_two_remainder_bound hf (neg_ne_zero.mpr hh.ne') hthird
  rw [abs_of_pos hh] at hp
  rw [abs_neg, abs_of_pos hh] at hm
  have hpl := (abs_le.mp hp).1
  have hpu := (abs_le.mp hp).2
  have hml := (abs_le.mp hm).1
  have hmu := (abs_le.mp hm).2
  have hz := abs_le.mp hzero
  have hph := abs_le.mp hplus
  have hmh := abs_le.mp hminus
  have hc : 0 ≤ M * h ^ 3 := mul_nonneg hM (pow_nonneg hh.le 3)
  by_cases hd : 0 ≤ iteratedDeriv 2 f 0
  · rw [abs_of_nonneg hd]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hd)]
    nlinarith


theorem first_derivative_two_point_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {M B h : ℝ} (hh : 0 < h) (_hM : 0 ≤ M)
    (hsecond : ∀ t, |iteratedDeriv 2 f t| ≤ M)
    (hzero : |f 0| ≤ B) (hplus : |f h| ≤ B) :
    |iteratedDeriv 1 f 0| * h ≤ 2 * B + M * h ^ 2 := by
  have hne : (0 : ℝ) ≠ h := Ne.symm hh.ne'
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  obtain ⟨ξ, _, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hne hf2.contDiffOn
  have hd : iteratedDerivWithin 1 f (uIcc 0 h) 0 = iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((hf.of_le (by simp)).contDiffAt) left_mem_uIcc
  have hp : taylorWithinEval f 1 (uIcc 0 h) 0 h = f 0 + h * iteratedDeriv 1 f 0 := by
    rw [taylorWithinEval_succ f 0]
    simp [hd]
  rw [hp] at he
  have hξ := abs_le.mp (hsecond ξ)
  have hz := abs_le.mp hzero
  have hhf := abs_le.mp hplus
  norm_num at he
  rw [iteratedDeriv_one]
  have hu := mul_le_mul_of_nonneg_right hξ.2 (sq_nonneg h)
  have hl := mul_le_mul_of_nonneg_right hξ.1 (sq_nonneg h)
  by_cases hs : 0 ≤ deriv f 0
  · rw [abs_of_nonneg hs]
    nlinarith [mul_nonneg _hM (sq_nonneg h)]
  · rw [abs_of_neg (lt_of_not_ge hs)]
    nlinarith [mul_nonneg _hM (sq_nonneg h)]


end ForcedComputation.VelocityDetector

end

end OAI

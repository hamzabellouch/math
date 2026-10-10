import Mathlib
import OAI.Combinatorics.KMedian.Analysis.Coefficients

namespace OAI

section
section
namespace MetricKMedian.Analytic

noncomputable def expApprox (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, u ^ k / (k.factorial : ℝ)

noncomputable def pTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 2))

noncomputable def aTaylor (n : ℕ) (x : ℝ) : ℝ :=
  3 - 2 * ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 1))

noncomputable def taylorError : ℝ := 14 / (6227020800 * 13)

theorem expApprox_error {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp u - expApprox 13 u| ≤ taylorError := by
  have he := Real.exp_bound (n := 13) hu (by decide)
  have hp : |u| ^ 13 ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
  have hmul := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 14 / (6227020800 * 13))
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd] at he
  exact he.trans (by norm_num [taylorError] at hmul ⊢; exact hmul)

private theorem expApprox_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => expApprox n (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold expApprox
  fun_prop

private theorem texpApprox_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * expApprox n (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold expApprox
  fun_prop

theorem integral_expApprox (n : ℕ) (x : ℝ) :
    (∫ t : ℝ in 0..1, expApprox n (-t * x)) =
      ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 1)) := by
  unfold expApprox
  rw [intervalIntegral.integral_finsetSum (fun _ _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  have hid : (fun t : ℝ => (-t * x) ^ k / (k.factorial : ℝ)) =
      (fun t : ℝ => ((-x) ^ k / (k.factorial : ℝ)) * t ^ k) := by
    funext t
    have he : -t * x = -x * t := by ring
    rw [he, mul_pow]
    ring
  rw [hid, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  simp only [div_mul_eq_div_div]
  ring

theorem integral_texpApprox (n : ℕ) (x : ℝ) :
    (∫ t : ℝ in 0..1, t * expApprox n (-t * x)) = pTaylor n x := by
  unfold expApprox pTaylor
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun _ _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  have hid : (fun t : ℝ => t * ((-t * x) ^ k / (k.factorial : ℝ))) =
      (fun t : ℝ => ((-x) ^ k / (k.factorial : ℝ)) * t ^ (k + 1)) := by
    funext t
    have he : -t * x = -x * t := by ring
    rw [he, mul_pow, pow_succ]
    ring
  rw [hid, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  simp only [Nat.cast_add, Nat.cast_one, div_mul_eq_div_div]
  ring

theorem P_taylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |P x - pTaylor 13 x| ≤ taylorError := by
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t * Real.exp (-t * x) - t * expApprox 13 (-t * x)‖ ≤ taylorError := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htx0 : 0 ≤ t * x := mul_nonneg ht.1.le hx0
    have htx1 : t * x ≤ 1 := by nlinarith [mul_le_mul ht.2 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 1)]
    have hex := expApprox_error (u := -t * x) (by
      rw [neg_mul, abs_neg, abs_of_nonneg htx0]
      exact htx1)
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1.le]
    have hm := mul_le_mul_of_nonneg_left hex ht.1.le
    have hu := mul_le_mul_of_nonneg_right ht.2 (by norm_num [taylorError] : 0 ≤ taylorError)
    exact hm.trans (by simpa only [one_mul] using hu)
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub (texp_integrable x) (texpApprox_integrable 13 x),
    integral_texpApprox] at he
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, P] using he

theorem A_taylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |A x - aTaylor 13 x| ≤ 2 * taylorError := by
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖Real.exp (-t * x) - expApprox 13 (-t * x)‖ ≤ taylorError := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htx0 : 0 ≤ t * x := mul_nonneg ht.1.le hx0
    have htx1 : t * x ≤ 1 := (mul_le_mul ht.2 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
    rw [Real.norm_eq_abs]
    apply expApprox_error
    rw [neg_mul, abs_neg, abs_of_nonneg htx0]
    exact htx1
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub (exp_integrable x) (expApprox_integrable 13 x),
    integral_expApprox] at he
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at he
  have hid : A x - aTaylor 13 x = -2 * ((∫ t : ℝ in 0..1, Real.exp (-t * x)) -
      ∑ k ∈ Finset.range 13, (-x) ^ k / ((k.factorial : ℝ) * (k + 1))) := by
    rw [A_eq, aTaylor]
    ring
  rw [hid, abs_mul]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left he (by norm_num)

end MetricKMedian.Analytic


end
end

end OAI

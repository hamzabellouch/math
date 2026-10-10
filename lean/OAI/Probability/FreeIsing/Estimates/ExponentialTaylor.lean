import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.ExponentialTaylor

theorem norm_exp_I_taylor_two_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have h := Complex.exp_bound (x := (x : ℂ) * Complex.I)
      (by simpa only [hnorm] using hx) (n := 3) (by norm_num)
    have heq : (∑ m ∈ Finset.range 3,
        ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [heq, hnorm] at h
    norm_num at h
    have heq' : Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
        (x : ℂ) ^ 2 / 2 =
        Complex.exp ((x : ℂ) * Complex.I) -
          (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) := by ring
    rw [heq']
    exact h.trans (by nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3])
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hsq : |x| ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
    have hcube : |x| ^ 2 ≤ |x| ^ 3 := by nlinarith [sq_nonneg (|x| - 1)]
    calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
          ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
          ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
          ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 + |x| + |x| ^ 2 / 2 := by norm_num
      _ ≤ 4 * |x| ^ 3 := by nlinarith

theorem norm_exp_I_mul_taylor_two_le (a x : ℝ) :
    ‖Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) - 1 -
      ((a * x : ℝ) : ℂ) * Complex.I + (((a * x : ℝ) : ℂ) ^ 2) / 2‖ ≤
      4 * |a| ^ 3 * |x| ^ 3 := by
  simpa only [abs_mul, mul_pow, mul_assoc] using norm_exp_I_taylor_two_le (a * x)

theorem norm_exp_neg_sub_one_add_le_sq {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp ((-x : ℝ) : ℂ) - 1 + (x : ℂ)‖ ≤ x ^ 2 := by
  have heq : Complex.exp ((-x : ℝ) : ℂ) - 1 + (x : ℂ) =
      ((Real.exp (-x) - 1 + x : ℝ) : ℂ) := by simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  by_cases hsmall : x ≤ 1
  · have h := Real.norm_exp_sub_one_sub_id_le (x := -x) (by simpa [abs_of_nonneg hx] using hsmall)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, sq_abs, neg_sq] using h
  · have hlarge : 1 ≤ x := (lt_of_not_ge hsmall).le
    have hnonneg : 0 ≤ Real.exp (-x) - 1 + x := by
      linarith [Real.add_one_le_exp (-x)]
    rw [abs_of_nonneg hnonneg]
    have hbound : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
    nlinarith

theorem norm_recurrence_error_le_sum
    (z a : ℕ → ℂ) (e : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1)
    (he : ∀ k < n, ‖z (k + 1) - a k * z k‖ ≤ e k) :
    ‖z n - (∏ k ∈ Finset.range n, a k) * z 0‖ ≤
      ∑ k ∈ Finset.range n, e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
      (fun k hk => he k (Nat.lt_succ_of_lt hk))
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have heq : z (n + 1) - ((∏ k ∈ Finset.range n, a k) * a n) * z 0 =
        (z (n + 1) - a n * z n) +
          a n * (z n - (∏ k ∈ Finset.range n, a k) * z 0) := by ring
    rw [heq]
    calc
      _ ≤ ‖z (n + 1) - a n * z n‖ +
          ‖a n * (z n - (∏ k ∈ Finset.range n, a k) * z 0)‖ := norm_add_le _ _
      _ ≤ e n + 1 * (∑ k ∈ Finset.range n, e k) := by
        apply add_le_add (he n (by omega))
        rw [norm_mul]
        exact mul_le_mul (ha n (by omega)) hprev (norm_nonneg _) (by norm_num)
      _ = _ := by ring

end Problem367.ExponentialTaylor

end

end OAI

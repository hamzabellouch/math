import OAI.Algebra.DepthFive.OccupationRatio

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Algebraic removal of the geometric normalization from the occupation ratio. -/
theorem occupationRatio_mul_mean_pow {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (H : ℕ) :
    occupationRatio t r H * (t / r) ^ H =
      (∏ j ∈ Finset.range H, (t - (j : ℝ))) /
        (∏ j ∈ Finset.range H, (r + (j : ℝ))) := by
  have hconst : (t / r) ^ H = ∏ _j ∈ Finset.range H, t / r := by simp [div_pow]
  rw [occupationRatio, hconst, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hsum : r + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hden : 1 + (j : ℝ) / r ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- The exact factorial-moment ratio over weak compositions. -/
theorem descFactorial_div_ascFactorial_eq_ratio {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : H ≤ t) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) =
      occupationRatio t r H * ((t : ℝ) / r) ^ H := by
  rw [occupationRatio_mul_mean_pow (by exact_mod_cast ht) (by exact_mod_cast hr)]
  congr 1
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_sub (le_trans (Finset.mem_range.mp hj).le hH)
  · rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_add r j

/-- Every factorial order admits the independent geometric upper comparison. -/
theorem descFactorial_div_ascFactorial_le_mean_pow {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) ≤ ((t : ℝ) / r) ^ H := by
  by_cases hH : H ≤ t
  · rw [descFactorial_div_ascFactorial_eq_ratio ht hr hH]
    have hratio := occupationRatio_le_one (t := (t : ℝ)) (r := (r : ℝ)) (H := H) (by exact_mod_cast ht)
      (by exact_mod_cast hr) (by exact_mod_cast hH)
    calc
      occupationRatio t r H * ((t : ℝ) / r) ^ H ≤ 1 * ((t : ℝ) / r) ^ H :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := one_mul _
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hH)]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- The lower comparison is uniform over all factorial orders up to half the total. -/
theorem exp_mul_mean_pow_le_descFactorial_div_ascFactorial {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : 2 * H ≤ t) :
    Real.exp (-(H : ℝ) ^ 2 / t - (H : ℝ) ^ 2 / (2 * r)) *
        ((t : ℝ) / r) ^ H ≤ (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  have hHt : H ≤ t := by omega
  rw [descFactorial_div_ascFactorial_eq_ratio ht hr hHt]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply exp_le_occupationRatio (by exact_mod_cast ht) (by exact_mod_cast hr)
  have hcast : 2 * (H : ℝ) ≤ t := by exact_mod_cast hH
  linarith

/-- A common loss bound can be used for all orders bounded by `H₀`. -/
theorem exp_mul_mean_pow_le_descFactorial_div_ascFactorial_of_le {t r H H₀ : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : H ≤ H₀) (hH₀ : 2 * H₀ ≤ t) :
    Real.exp (-(H₀ : ℝ) ^ 2 / t - (H₀ : ℝ) ^ 2 / (2 * r)) *
        ((t : ℝ) / r) ^ H ≤ (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  apply le_trans _ (exp_mul_mean_pow_le_descFactorial_div_ascFactorial ht hr
    (show 2 * H ≤ t by omega))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : (H : ℝ) ^ 2 ≤ (H₀ : ℝ) ^ 2 := by
    have hh : (H : ℝ) ≤ H₀ := by exact_mod_cast hH
    nlinarith [show 0 ≤ (H : ℝ) by positivity]
  have h₁ := div_le_div_of_nonneg_right hsq (show 0 ≤ (t : ℝ) by positivity)
  have h₂ := div_le_div_of_nonneg_right hsq (show 0 ≤ 2 * (r : ℝ) by positivity)
  simp only [neg_div]
  linarith

/-- Zero total occupation is also allowed in the geometric upper comparison. -/
theorem descFactorial_div_ascFactorial_le_mean_pow_of_pos {t r H : ℕ} (hr : 0 < r) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) ≤ ((t : ℝ) / r) ^ H := by
  by_cases ht : 0 < t
  · exact descFactorial_div_ascFactorial_le_mean_pow ht hr
  · have ht0 : t = 0 := by omega
    subst t
    cases H with
    | zero => simp
    | succ H => simp [Nat.descFactorial_succ]

end Problem335

end

end OAI

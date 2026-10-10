import OAI.Algebra.DepthFive.OccupationRatioAlgebra

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- A common loss bound can be used for all orders bounded by `H₀`. -/
theorem occupation_factorial_ratio_lower_of_le {t r H H₀ : ℕ}
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

/-- Termwise occupation comparison for every nonnegative factorial-basis expansion. -/
theorem weighted_factorialMoment_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (H : ι → ℕ) {t r : ℕ} (hr : 0 < r)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i * ((t.descFactorial (H i) : ℝ) / (r.ascFactorial (H i) : ℝ))) ≤
      ∑ i ∈ s, c i * ((t : ℝ) / r) ^ H i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (descFactorial_div_ascFactorial_le_mean_pow_of_pos hr)
    (hc i hi)

/-- Uniform lower occupation comparison for a nonnegative finite expansion. -/
theorem exp_mul_weighted_mean_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (H : ι → ℕ) {t r H₀ : ℕ} (ht : 0 < t) (hr : 0 < r)
    (hH₀ : 2 * H₀ ≤ t) (hc : ∀ i ∈ s, 0 ≤ c i) (hH : ∀ i ∈ s, H i ≤ H₀) :
    Real.exp (-(H₀ : ℝ) ^ 2 / t - (H₀ : ℝ) ^ 2 / (2 * r)) *
        (∑ i ∈ s, c i * ((t : ℝ) / r) ^ H i) ≤
      ∑ i ∈ s, c i * ((t.descFactorial (H i) : ℝ) / (r.ascFactorial (H i) : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = c i * (Real.exp (-(H₀ : ℝ) ^ 2 / t - (H₀ : ℝ) ^ 2 / (2 * r)) *
        ((t : ℝ) / r) ^ H i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (occupation_factorial_ratio_lower_of_le ht hr (hH i hi) hH₀)
      (hc i hi)

/-- Independent variable groups multiply their moment comparisons and add losses. -/
theorem two_group_factorial_ratio_lower_of_le {a v b u h k H J : ℕ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (hu : 0 < u)
    (hh : h ≤ H) (hk : k ≤ J) (hH : 2 * H ≤ a) (hJ : 2 * J ≤ b) :
    Real.exp ((-(H : ℝ) ^ 2 / a - (H : ℝ) ^ 2 / (2 * v)) +
        (-(J : ℝ) ^ 2 / b - (J : ℝ) ^ 2 / (2 * u))) *
      (((a : ℝ) / v) ^ h * ((b : ℝ) / u) ^ k) ≤
    ((a.descFactorial h : ℝ) / (v.ascFactorial h : ℝ)) *
      ((b.descFactorial k : ℝ) / (u.ascFactorial k : ℝ)) := by
  have h₁ := occupation_factorial_ratio_lower_of_le ha hv hh hH
  have h₂ := occupation_factorial_ratio_lower_of_le hb hu hk hJ
  have hprod := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  rw [Real.exp_add]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- Upper comparison for nonnegative expansions in two independent groups. -/
theorem weighted_two_group_factorialMoment_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (h k : ι → ℕ) {a v b u : ℕ} (hv : 0 < v) (hu : 0 < u)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i *
      (((a.descFactorial (h i) : ℝ) / (v.ascFactorial (h i) : ℝ)) *
       ((b.descFactorial (k i) : ℝ) / (u.ascFactorial (k i) : ℝ)))) ≤
    ∑ i ∈ s, c i * (((a : ℝ) / v) ^ h i * ((b : ℝ) / u) ^ k i) := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  exact mul_le_mul (descFactorial_div_ascFactorial_le_mean_pow_of_pos hv)
    (descFactorial_div_ascFactorial_le_mean_pow_of_pos hu) (by positivity) (by positivity)

/-- Uniform lower comparison for the two-group factorial expansions in both traces. -/
theorem exp_mul_weighted_two_group_mean_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (h k : ι → ℕ) {a v b u H J : ℕ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (hu : 0 < u)
    (hH : 2 * H ≤ a) (hJ : 2 * J ≤ b) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hh : ∀ i ∈ s, h i ≤ H) (hk : ∀ i ∈ s, k i ≤ J) :
    Real.exp ((-(H : ℝ) ^ 2 / a - (H : ℝ) ^ 2 / (2 * v)) +
        (-(J : ℝ) ^ 2 / b - (J : ℝ) ^ 2 / (2 * u))) *
      (∑ i ∈ s, c i * (((a : ℝ) / v) ^ h i * ((b : ℝ) / u) ^ k i)) ≤
    ∑ i ∈ s, c i *
      (((a.descFactorial (h i) : ℝ) / (v.ascFactorial (h i) : ℝ)) *
       ((b.descFactorial (k i) : ℝ) / (u.ascFactorial (k i) : ℝ))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = c i * (Real.exp ((-(H : ℝ) ^ 2 / a - (H : ℝ) ^ 2 / (2 * v)) +
        (-(J : ℝ) ^ 2 / b - (J : ℝ) ^ 2 / (2 * u))) *
      (((a : ℝ) / v) ^ h i * ((b : ℝ) / u) ^ k i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (two_group_factorial_ratio_lower_of_le ha hv hb hu (hh i hi) (hk i hi) hH hJ)
      (hc i hi)

end Problem335

end

end OAI

import OAI.Algebra.DepthFive.BinomialRatios

namespace OAI

namespace Problem335

/-- A uniform Bernoulli bound for the rounding correction in the descending
homogeneous-space dimension ratio. -/
theorem inverse_one_sub_pow_le_two (N : ℝ) (I : ℕ)
    (hN : 1 ≤ N) (hI : 2 * (I : ℝ) ≤ N) :
    ((1 - 1 / N) ^ I)⁻¹ ≤ 2 := by
  have hNpos : 0 < N := by linarith
  have hinv : 1 / N ≤ 1 := (div_le_one hNpos).2 hN
  have hber := one_add_mul_le_pow (a := -(1 / N)) (by linarith : -2 ≤ -(1 / N)) I
  have hfrac : (I : ℝ) / N ≤ 1 / 2 := (div_le_iff₀ hNpos).2 (by linarith)
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 1 / N) ^ I := by
    simp only [mul_neg, mul_one_div, ← sub_eq_add_neg] at hber
    nlinarith
  have hpow : 0 < (1 - 1 / N) ^ I := lt_of_lt_of_le (by norm_num) hhalf
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpow).2
  linarith

/-- Real-exponent version of the preceding natural-power estimate. -/
theorem one_sub_rpow_neg_nat_le_two (N : ℝ) (I : ℕ)
    (hN : 1 ≤ N) (hI : 2 * (I : ℝ) ≤ N) :
    (1 - 1 / N) ^ (-(I : ℝ)) ≤ 2 := by
  have hbase : 0 ≤ 1 - 1 / N := by
    have hNpos : 0 < N := by linarith
    have := (div_le_one hNpos).2 hN
    linarith
  rw [Real.rpow_neg hbase, Real.rpow_natCast]
  exact inverse_one_sub_pow_le_two N I hN hI

/-- Rounding loss and the balanced multiplication cost combine into one
absolute-discrepancy exponent. -/
theorem corrected_ratio_product_le (α β N ρ : ℝ) (I J : ℕ)
    (hα : 0 < α) (hβ : α ^ ρ ≤ β)
    (hN : 1 ≤ N) (hI : 2 * (I : ℝ) ≤ N) :
    (α / (1 - 1 / N)) ^ I * β ^ (-(J : ℝ)) ≤
      2 * α ^ ((I : ℝ) - ρ * J) := by
  have hβpos : 0 < β := lt_of_lt_of_le (Real.rpow_pos_of_pos hα _) hβ
  have hdown : (α / (1 - 1 / N)) ^ I ≤ 2 * α ^ I := by
    rw [div_pow, div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_left (inverse_one_sub_pow_le_two N I hN hI)
      (pow_nonneg hα.le I)
    simpa only [mul_comm] using this
  have hup := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hα ρ) hβ
    (neg_nonpos.mpr (Nat.cast_nonneg J))
  rw [← Real.rpow_mul hα.le] at hup
  calc
    _ ≤ (2 * α ^ I) * α ^ (ρ * -(J : ℝ)) :=
      mul_le_mul hdown hup (Real.rpow_nonneg hβpos.le _) (by positivity)
    _ = 2 * α ^ ((I : ℝ) - ρ * J) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hα]
      congr 2
      ring

/-- The exact intermediate-dimension bound after the harmless rounding factor
has been absorbed. The hypotheses are purely numerical and field-independent. -/
theorem intermediate_dimension_ratio_le_balanced {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b) (hI : I ≤ a)
    (hbudget : 2 * I ≤ a + v) (ρ : ℝ)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    ((homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J)) /
        ((homogeneousDim v a : ℝ) * homogeneousDim u b) ≤
      2 * ((a : ℝ) / ((a : ℝ) + v)) ^ ((I : ℝ) - ρ * J) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hN : (1 : ℝ) < (a : ℝ) + v := by linarith
  have hdown : (a : ℝ) / ((a : ℝ) + v - 1) =
      ((a : ℝ) / ((a : ℝ) + v)) / (1 - 1 / ((a : ℝ) + v)) := by
    field_simp
  have hup : (((b : ℝ) + u) / b) ^ J =
      ((b : ℝ) / ((b : ℝ) + u)) ^ (-(J : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow, inv_div]
  calc
    _ ≤ ((a : ℝ) / ((a : ℝ) + v - 1)) ^ I *
        (((b : ℝ) + u) / b) ^ J := intermediate_dimension_ratio_le hv hu hb hI
    _ = ((((a : ℝ) / ((a : ℝ) + v)) / (1 - 1 / ((a : ℝ) + v))) ^ I) *
        ((b : ℝ) / ((b : ℝ) + u)) ^ (-(J : ℝ)) := by rw [hdown, hup]
    _ ≤ _ := corrected_ratio_product_le _ _ _ ρ I J (by positivity) hbalance hN.le
      (by exact_mod_cast hbudget)

/-- Unnormalized form of the balanced intermediate-dimension estimate. -/
theorem intermediate_dimension_le_balanced {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b) (hI : I ≤ a)
    (hbudget : 2 * I ≤ a + v) (ρ : ℝ)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ((a : ℝ) / ((a : ℝ) + v)) ^ ((I : ℝ) - ρ * J) := by
  have hd : (0 : ℝ) < (homogeneousDim v a : ℝ) * homogeneousDim u b := by
    exact mul_pos (by exact_mod_cast homogeneousDim_pos hv a)
      (by exact_mod_cast homogeneousDim_pos hu b)
  have h := (div_le_iff₀ hd).mp
    (intermediate_dimension_ratio_le_balanced (J := J) hv hu ha hb hI hbudget ρ hbalance)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end Problem335

end OAI

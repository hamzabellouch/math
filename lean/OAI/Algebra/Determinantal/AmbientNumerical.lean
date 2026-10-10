import OAI.Algebra.Determinantal.BorderPolars

namespace OAI

namespace PermanentBorder.Polar

/-- The binomial count implies a numerical lower bound for the matrix size.
No positivity assumption on `D` or `n` is needed. -/
theorem ambient_count_numerical_bound (n K D : ℕ)
    (hcount : D ≤ 2 ^ K * (2 * n - 1).choose (K + 1)) :
    ((K + 1 : ℕ) : ℝ) / (4 * Real.exp 1) *
      Real.rpow (D : ℝ) (1 / ((K + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hcountR : (D : ℝ) ≤ 2 ^ K * ((2 * n - 1).choose (K + 1) : ℝ) := by
    exact_mod_cast hcount
  have hchoose := choose_exp_bound (2 * n - 1) (K + 1) (by omega)
  have htwo : ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * n := by
    exact_mod_cast (Nat.sub_le (2 * n) 1)
  have hbase : Real.exp 1 * ((2 * n - 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) ≤
      (2 * Real.exp 1 * n) / (K + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hpow : (D : ℝ) ≤ (4 * Real.exp 1 * n / (K + 1)) ^ (K + 1) := by
    calc
      (D : ℝ) ≤ 2 ^ K * ((2 * n - 1).choose (K + 1) : ℝ) := hcountR
      _ ≤ 2 ^ K * (Real.exp 1 * ((2 * n - 1 : ℕ) : ℝ) /
          ((K + 1 : ℕ) : ℝ)) ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ ≤ 2 ^ (K + 1) * ((2 * Real.exp 1 * n) / (K + 1)) ^ (K + 1) := by
        apply mul_le_mul
        · have htwoPow : (2 : ℝ) ^ K ≤ 2 ^ (K + 1) := by
            rw [pow_succ]
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
          exact htwoPow
        · exact pow_le_pow_left₀ (by positivity) hbase _
        · positivity
        · positivity
      _ = (4 * Real.exp 1 * n / (K + 1)) ^ (K + 1) := by
        rw [← mul_pow]
        congr 1
        ring
  have hrootpow :
      (Real.rpow (D : ℝ) (1 / ((K + 1 : ℕ) : ℝ))) ^ (K + 1) = (D : ℝ) := by
    simpa only [one_div, Real.rpow_eq_pow] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg D) (by omega : K + 1 ≠ 0))
  have hroot_nonneg : 0 ≤ Real.rpow (D : ℝ) (1 / ((K + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_eq_pow]
    exact Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hle : Real.rpow (D : ℝ) (1 / ((K + 1 : ℕ) : ℝ)) ≤
      4 * Real.exp 1 * n / (K + 1) := by
    apply (pow_le_pow_iff_left₀ hroot_nonneg (by positivity)
      (by omega : K + 1 ≠ 0)).mp
    rw [hrootpow]
    exact hpow
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.exp 1)).mpr
  have h := (le_div_iff₀ hK).mp hle
  simp only [Nat.cast_add, Nat.cast_one] at h ⊢
  nlinarith

end PermanentBorder.Polar

end OAI

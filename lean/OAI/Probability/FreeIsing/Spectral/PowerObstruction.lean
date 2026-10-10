import Mathlib

namespace OAI

namespace Problem367

open Filter Topology

theorem le_one_of_pow_le_affine {q a c : ℝ}
    (h : ∀ n : ℕ, q ^ n ≤ a + c * (n : ℝ)) : q ≤ 1 := by
  by_contra hq
  have hq1 : 1 < q := lt_of_not_ge hq
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hconst : Tendsto (fun n : ℕ => a / q ^ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_pow_const_div_const_pow_of_one_lt 0 hq1).const_mul a
  have hlinear : Tendsto (fun n : ℕ => c * ((n : ℝ) / q ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 hq1).const_mul c
  have hlim : Tendsto (fun n : ℕ => (a + c * (n : ℝ)) / q ^ n)
      atTop (𝓝 0) := by
    simpa [add_div, mul_div_assoc] using hconst.add hlinear
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim fun n => by
    exact (le_div_iff₀ (pow_pos hq0 n)).2 (by simpa using h n)
  exact (not_le_of_gt zero_lt_one) hfalse

theorem le_inv_sqrt_of_normalized_pow_bound {theta b a c : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ, (theta * Real.sqrt b) ^ n ≤ a + c * (n : ℝ)) :
    theta ≤ 1 / Real.sqrt b := by
  apply (le_div_iff₀ (Real.sqrt_pos.2 hb)).2
  exact le_one_of_pow_le_affine h

theorem le_inv_sqrt_of_pow_bound {theta b a c : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ,
      theta ^ n ≤ (a + c * (n : ℝ)) * (Real.sqrt b)⁻¹ ^ n) :
    theta ≤ 1 / Real.sqrt b := by
  apply le_inv_sqrt_of_normalized_pow_bound hb
  intro n
  rw [mul_pow]
  calc
    theta ^ n * Real.sqrt b ^ n ≤
        ((a + c * (n : ℝ)) * (Real.sqrt b)⁻¹ ^ n) * Real.sqrt b ^ n :=
      mul_le_mul_of_nonneg_right (h n) (pow_nonneg (Real.sqrt_nonneg b) n)
    _ = a + c * (n : ℝ) := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (Real.sqrt_pos.2 hb).ne',
        one_pow, mul_one]

theorem threshold_of_bsv_pow_bound {d : ℕ} {theta : ℝ} (hd : 3 ≤ d)
    (h : ∀ n : ℕ,
      theta ^ n ≤ (1 + (((d : ℝ) - 2) / (d : ℝ)) * (n : ℝ)) *
        (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact le_inv_sqrt_of_pow_bound (by linarith) h

end Problem367

end OAI

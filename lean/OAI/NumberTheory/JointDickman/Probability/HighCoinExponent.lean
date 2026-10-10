import OAI.NumberTheory.JointDickman.Amplification.AmplificationScaleSum

namespace OAI

/-! # The four high-prime factors after averaging the remaining subsets -/

namespace JointDickman

/-- The count cutoff's fourth power is exactly the required scale decay. -/
theorem high_coin_cutoff_identity {B Y C : ℝ} (hB : 0 < B) (hY : 0 < Y) :
    ((1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C))^4 =
      (2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add]
  congr 1
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hlog : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [hhalf, hlog]
  unfold amplificationExponent
  ring

theorem high_coin_four_factor_bound {B Y C x y : ℝ} {a d : ℕ}
    (hB : 0 < B) (hY : 0 < Y)
    (ha : (2 / 5 : ℝ) * Real.log (B / Y) - C ≤ (a : ℝ))
    (hd : (2 / 5 : ℝ) * Real.log (B / Y) - C ≤ (d : ℝ))
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxbound : x ≤ (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C))
    (hybound : y ≤ (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C)) :
    (1 / 2 : ℝ)^a * (1 / 2 : ℝ)^d * (x * y) ≤
      (2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent := by
  let q := (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hpa : (1 / 2 : ℝ)^a ≤ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha
  have hpd : (1 / 2 : ℝ)^d ≤ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hd
  have h1 := mul_le_mul hpa hpd (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ)^d) hq
  have h2 := mul_le_mul hxbound hybound hy hq
  have hh := mul_le_mul h1 h2 (mul_nonneg hx hy) (mul_nonneg hq hq)
  calc
    _ ≤ q * q * (q * q) := hh
    _ = q^4 := by ring
    _ = _ := high_coin_cutoff_identity hB hY

end JointDickman

end OAI

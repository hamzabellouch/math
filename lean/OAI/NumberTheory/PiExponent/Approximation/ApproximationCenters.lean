import Mathlib

namespace OAI

namespace PiExponent

noncomputable def approximatePeriod (p : ℤ) (q : ℕ) : ℂ :=
  2 * Complex.I * (p : ℂ) / (q : ℂ)

theorem approximatePeriod_ne_zero {p : ℤ} {q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) :
    approximatePeriod p q ≠ 0 := by
  unfold approximatePeriod
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hp))
    (by exact_mod_cast hq)

theorem approximation_centers_injective {p : ℤ} {q : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    Function.Injective (fun j : ℕ => (j : ℂ) * approximatePeriod p q) := by
  intro j k h
  have heq : (j : ℂ) = (k : ℂ) := mul_right_cancel₀ (approximatePeriod_ne_zero hp hq) h
  exact_mod_cast heq

noncomputable def logarithmicPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem norm_period_error (p : ℤ) (q : ℕ) :
    ‖approximatePeriod p q - logarithmicPeriod‖ =
      2 * |Real.pi - (p : ℝ) / q| := by
  have heq : approximatePeriod p q - logarithmicPeriod =
      (2 * Complex.I) * (((p : ℝ) / q - Real.pi : ℝ) : ℂ) := by
    unfold approximatePeriod logarithmicPeriod
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num [norm_mul, abs_sub_comm]

theorem norm_center_error_le (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hj : j ≤ K)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * (approximatePeriod p q - logarithmicPeriod)‖ ≤
      2 * K * (q : ℝ) ^ (-nu) := by
  rw [norm_mul, norm_period_error]
  have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
  have hqpow : 0 ≤ (q : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  simp only [Complex.norm_natCast]
  nlinarith [abs_nonneg (Real.pi - (p : ℝ) / q)]

theorem ceil_log_bounds {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ (⌈Real.log q⌉₊ : ℝ) - Real.log q ∧
      (⌈Real.log q⌉₊ : ℝ) - Real.log q < 1 := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  constructor
  · exact sub_nonneg.mpr (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one hlog
    linarith

theorem rpow_neg_le_exp_ceil_log (nu : ℝ) {q : ℕ} (hnu : 0 ≤ nu) (hq : 1 ≤ q) :
    (q : ℝ) ^ (-nu) ≤
      Real.exp nu * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Real.rpow_def_of_pos hqpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw := (ceil_log_bounds hq).2
  nlinarith

theorem norm_center_error_exp (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hnu : 0 ≤ nu) (hq : 1 ≤ q) (hj : j ≤ K)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * (approximatePeriod p q - logarithmicPeriod)‖ ≤
      (2 * K * Real.exp nu) * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ)) := by
  calc
    _ ≤ 2 * K * (q : ℝ) ^ (-nu) := norm_center_error_le nu hj happrox
    _ ≤ 2 * K * (Real.exp nu * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu hq) (by positivity)
    _ = _ := by ring

end PiExponent

end OAI

import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Explicit derivatives of the reciprocal phase used in deterministic cancellation. -/
theorem reciprocal_phase_iteratedDeriv (k : ℕ) (Z x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Z / y) x =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * Z / x ^ (k + 1) := by
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  ring

theorem abs_reciprocal_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv k (fun y : ℝ => Z / y) x| =
      (k.factorial : ℝ) * |Z| / x ^ (k + 1) := by
  rw [reciprocal_phase_iteratedDeriv]
  simp [abs_div, abs_mul, abs_pow, abs_of_pos hx]

/-- Uniform derivative bounds on a dyadic interval. -/
theorem reciprocal_phase_derivative_bounds (k : ℕ) (Z : ℝ) {U x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hx2 : x ≤ 2 * U) :
    (k.factorial : ℝ) * |Z| / (2 * U) ^ (k + 1) ≤
        |iteratedDeriv k (fun y : ℝ => Z / y) x| ∧
      |iteratedDeriv k (fun y : ℝ => Z / y) x| ≤
        (k.factorial : ℝ) * |Z| / U ^ (k + 1) := by
  have hx0 : 0 < x := hU.trans_le hx
  rw [abs_reciprocal_phase_iteratedDeriv k Z hx0]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) 
    exact pow_le_pow_left₀ (by positivity) hx2 _
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hU _)
    exact pow_le_pow_left₀ hU.le hx _

/-- The same derivative estimate on an arbitrary positive interval. The flexible
upper endpoint allows the extra samples used in a second-derivative test. -/
theorem reciprocal_phase_derivative_bounds_interval (k : ℕ) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x ≤ V) :
    (k.factorial : ℝ) * |Z| / V ^ (k + 1) ≤
        |iteratedDeriv k (fun y : ℝ => Z / y) x| ∧
      |iteratedDeriv k (fun y : ℝ => Z / y) x| ≤
        (k.factorial : ℝ) * |Z| / U ^ (k + 1) := by
  have hx0 : 0 < x := hU.trans_le hx
  rw [abs_reciprocal_phase_iteratedDeriv k Z hx0]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _)
    exact pow_le_pow_left₀ hx0.le hxV _
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hU _)
    exact pow_le_pow_left₀ hU.le hx _

end Problem337

end

end OAI

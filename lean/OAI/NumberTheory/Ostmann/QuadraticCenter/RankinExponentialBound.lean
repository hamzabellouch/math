import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.QuadraticCenter.HalfKernelRankin

namespace OAI

/-! # An explicit numerical margin in the high-weight Rankin parameter -/

namespace Ostmann

/-- The large negative Rankin exponent dominates with ample margin once the
stated logarithmic and positive-error bounds hold. -/
theorem rankin_exponential_bound (T u K E : ℝ) (b : ℕ)
    (hT : 1 < T) (hu : 1 < u) (hK : 0 ≤ K)
    (hlog : Real.log u ≤ Real.log T / 100000)
    (hb : K / (400 * Real.log u) - 1 ≤ b)
    (hE : Real.log u + Real.log T / 4 + E ≤ K) :
    u * ((T ^ (1 / 4 : ℝ)) ^ b)⁻¹ * Real.exp E ≤ Real.exp (-20 * K) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hlt : 0 < Real.log T := Real.log_pos hT
  have hb' : K ≤ ((b : ℝ) + 1) * (400 * Real.log u) := by
    apply (div_le_iff₀ (by positivity : 0 < 400 * Real.log u)).mp
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (b : ℝ) + 1 by positivity)
  have hexp : Real.log u - (b : ℝ) * (Real.log T / 4) + E ≤ -20 * K := by
    nlinarith
  have hp : (T ^ (1 / 4 : ℝ)) ^ b = Real.exp ((b : ℝ) * (Real.log T / 4)) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp, ← Real.exp_neg]
  calc
    _ = Real.exp (Real.log u - (b : ℝ) * (Real.log T / 4) + E) := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hu0, div_eq_mul_inv, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexp

end Ostmann

end OAI

import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # A geometric moment bound uniform in the integer exponent -/

namespace RegularPointCoordinates

theorem power_growth_geometric_bound {C A t E : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (ht : t ≤ 1) (j : ℕ)
    (hE : E+1 ≤ Real.exp (C*(j+1:ℝ)*t)*(A^(j+1)+1)) :
    E ≤ 2*(max 1 A*Real.exp C)^(j+2) := by
  let B := max 1 A
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hAe : A^(j+1) ≤ B^(j+1) := pow_le_pow_left₀ hA (le_max_right _ _) _
  have hone : 1 ≤ B^(j+1) := one_le_pow₀ hB
  have he : Real.exp (C*(j+1:ℝ)*t) ≤ (Real.exp C)^(j+1) := by
    calc
      _ ≤ Real.exp (C*(j+1:ℝ)) := Real.exp_le_exp.mpr
        (mul_le_of_le_one_right (by positivity) ht)
      _ = _ := by rw [mul_comm C,← Nat.cast_add_one,Real.exp_nat_mul]
  have hprod := mul_le_mul he (show A^(j+1)+1 ≤ 2*B^(j+1) by linarith)
    (by positivity) (by positivity)
  have hpow : 1 ≤ B*Real.exp C := by
    have hexp : 1 ≤ Real.exp C := Real.one_le_exp_iff.mpr hC
    nlinarith
  have hstep : (B*Real.exp C)^(j+1) ≤ (B*Real.exp C)^(j+2) := by
    have hp := mul_le_mul_of_nonneg_left hpow (pow_nonneg (zero_le_one.trans hpow) (j+1))
    simpa only [mul_one,pow_succ] using hp
  have hid : (Real.exp C)^(j+1)*(2*B^(j+1)) = 2*(B*Real.exp C)^(j+1) := by
    rw [mul_pow]
    ring
  rw [hid] at hprod
  change E ≤ 2*(B*Real.exp C)^(j+2)
  linarith only [hE,hprod,hstep]

end RegularPointCoordinates

end OAI

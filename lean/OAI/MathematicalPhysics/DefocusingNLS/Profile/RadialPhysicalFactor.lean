import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! Elementary norm identities for the radial complex power. -/

namespace DefocusingNLS

theorem radialPhysicalFactor_norm (ν : ℂ) (r : ℝ) (hr : 0 < r) :
    ‖Complex.exp (ν*(Real.log r : ℂ))‖ = r^ν.re := by
  rw [Complex.norm_exp,Real.rpow_def_of_pos hr]
  congr 1
  simp [Complex.mul_re,mul_comm]

theorem radialPhysicalFactor_norm_power (k : ℕ) (hk : 0 < k) (b r : ℝ) (hr : 0 < r) :
    ‖Complex.exp ((-1/(k : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))‖^(2*k)=1/r^2 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have he : ((-1/(k : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ)).re=
      -(Real.log r)/(k : ℝ) := by
    simp [Complex.mul_re,Complex.mul_im,Complex.div_re]
    field_simp
  rw [Complex.norm_exp,he,← Real.exp_nat_mul]
  have hexp : ((2*k : ℕ) : ℝ)*(-(Real.log r)/(k : ℝ))=-(2*Real.log r) := by
    push_cast
    field_simp
  rw [hexp,Real.exp_neg,two_mul,Real.exp_add,Real.exp_log hr]
  simp [pow_two,one_div]

end DefocusingNLS

end OAI

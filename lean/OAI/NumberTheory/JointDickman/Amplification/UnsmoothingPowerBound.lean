import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Balancing the two errors in a logarithmic finite difference -/
namespace JointDickman

theorem unsmoothing_power_bound {x l B β γ μ C M : ℝ}
    (hx : 0 < x) (hl : 1 ≤ l) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hβ : β+B ≤ μ) (hγ : γ-B ≤ μ) :
    (M*l^γ)*(x/l^B)+2*(C*x^2*l^β)/(x/l^B) ≤ (M+2*C)*x*l^μ := by
  have hl0 : 0 < l := by linarith
  have hpow : 0 < l^B := Real.rpow_pos_of_pos hl0 B
  have hfirst : (M*l^γ)*(x/l^B) = M*x*l^(γ-B) := by
    rw [Real.rpow_sub hl0]
    ring
  have hsecond : 2*(C*x^2*l^β)/(x/l^B) = 2*C*x*l^(β+B) := by
    rw [Real.rpow_add hl0]
    field_simp
  rw [hfirst,hsecond]
  have hb := Real.rpow_le_rpow_of_exponent_le hl hβ
  have hg := Real.rpow_le_rpow_of_exponent_le hl hγ
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*C*x by positivity),
    mul_le_mul_of_nonneg_left hg (show 0 ≤ M*x by positivity)]

end JointDickman

end OAI

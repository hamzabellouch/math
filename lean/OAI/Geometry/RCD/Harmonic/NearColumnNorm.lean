import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! # Recovering a norm from one nearby quadratic column estimate -/

open scoped InnerProductSpace
namespace RegularPointCoordinates

theorem near_column_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) {d e q : ℝ} (hd : 0≤d) (he : 0≤e)
    (hnear : ‖w-z‖≤q)
    (hcol : ⟪z,w⟫_ℝ^2≤d^2*‖w‖^2*(1+e)) :
    ‖w‖≤d*Real.sqrt (1+e)+q := by
  have hq : 0≤q := (norm_nonneg _).trans hnear
  have hs : (Real.sqrt (1+e))^2=1+e := Real.sq_sqrt (by linarith)
  have hb : |⟪z,w⟫_ℝ|≤d*‖w‖*Real.sqrt (1+e) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    calc
      _≤d^2*‖w‖^2*(1+e) := hcol
      _=(d*‖w‖*Real.sqrt (1+e))^2 := by rw [mul_pow,mul_pow,hs]
  have hc := (real_inner_le_norm (w-z) w).trans
    (mul_le_mul_of_nonneg_right hnear (norm_nonneg w))
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hc
  have hh := (le_abs_self ⟪z,w⟫_ℝ).trans hb
  by_cases hw : ‖w‖=0
  · rw [hw]
    positivity
  · have hp : 0<‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    nlinarith

end RegularPointCoordinates

end OAI

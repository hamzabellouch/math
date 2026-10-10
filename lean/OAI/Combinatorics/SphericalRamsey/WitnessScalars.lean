import OAI.Combinatorics.SphericalRamsey.Parameter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
namespace GrahamSpherical

theorem parameter_den_pos : 0 < 1 + parameter ^ 2 := by positivity

theorem u_sq_add_v_sq : u ^ 2 + v ^ 2 = 1 := by
  unfold u v
  field_simp [ne_of_gt parameter_den_pos]
  ring

theorem v_pos : 0 < v := by
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  exact div_pos (mul_pos (by norm_num) ht) parameter_den_pos

theorem v_lt_u : v < u := by
  apply (div_lt_div_iff_of_pos_right parameter_den_pos).2
  have ht := parameter_bounds
  have hprod : 0 ≤ (12 / 100 - parameter) * (12 / 100 + parameter) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem u_lt_one : u < 1 := by
  change (1 - parameter ^ 2) / (1 + parameter ^ 2) < 1
  apply (div_lt_one parameter_den_pos).2
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  nlinarith [sq_pos_of_pos ht]

theorem u_pos : 0 < u := lt_trans v_pos v_lt_u

end GrahamSpherical

end

end OAI

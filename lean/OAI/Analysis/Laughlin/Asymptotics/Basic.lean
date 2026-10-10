import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin

theorem tail_series_value :
    HasSum (fun m : ℕ =>
      (3/2 : ℝ) * (3 * (17 + 2*(m : ℝ)) - 1) * (18 + 2*(m : ℝ)) *
        (1/2 : ℝ)^(17+2*m)) (61/4096 : ℝ) := by
  have hr : ‖(1/4 : ℝ)‖ < 1 := by norm_num
  have h₂ := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h₁ := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h₀ := hasSum_geometric_of_norm_lt_one hr
  have hs := (((h₂.mul_left (24 : ℝ)).add (h₁.mul_left 172)).add
    (h₀.mul_left 876)).mul_left (3/262144 : ℝ)
  convert! hs using 1
  · ext m
    have hc : (Nat.choose (m+2) 2 : ℝ) * 2 = ((m : ℝ)+2)*((m : ℝ)+1) := by
      have hx : (Nat.choose (m+2) 2 : ℝ) * 2 = ((m : ℝ)+2)*((m : ℝ)+1) := by
        induction m with
        | zero => norm_num
        | succ m ih =>
          rw [Nat.choose_succ_succ', Nat.choose_one_right]
          push_cast
          nlinarith
      exact hx
    have hp : (1/2 : ℝ)^(17+2*m) = (1/2 : ℝ)^17 * (1/4 : ℝ)^m := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hp]
    linear_combination -(9/65536 : ℝ) * (1/4 : ℝ)^m * hc
  · norm_num

end Laughlin

end OAI

import OAI.Geometry.ProjectionVolume.Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace Paper092

theorem simplex_constant_product_ratio (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    simplexConstant r * simplexConstant s / simplexConstant (r + s) =
      ((r + 1 : ℝ) * (s + 1) / (r + s + 1)) * (Nat.choose (r + s) r : ℝ) *
        ((r : ℝ) ^ r * (s : ℝ) ^ s / ((r + s : ℕ) : ℝ) ^ (r + s)) := by
  have hfac := Nat.choose_mul_factorial_mul_factorial (show r ≤ r + s by omega)
  simp only [Nat.add_sub_cancel_left] at hfac
  have hfac' : (Nat.choose (r + s) r : ℝ) * r.factorial * s.factorial =
      ((r + s).factorial : ℝ) := by exact_mod_cast hfac
  have hr0 : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hs0 : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have hrs0 : ((r + s : ℕ) : ℝ) ≠ 0 := by positivity
  have hrs1 : (r : ℝ) + s + 1 ≠ 0 := by positivity
  have hfrs0 : ((r + s).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r + s)
  unfold simplexConstant
  push_cast
  field_simp
  nlinarith [hfac']

theorem dimension_twenty_ratio :
    simplexConstant 10 * simplexConstant 10 / simplexConstant 20 =
      (22355476 : ℝ) / 22020096 := by
  norm_num [simplexConstant, Nat.factorial]

theorem dimension_twenty_strict :
    simplexConstant 20 < simplexConstant 10 * simplexConstant 10 := by
  norm_num [simplexConstant, Nat.factorial]

end Paper092

end OAI

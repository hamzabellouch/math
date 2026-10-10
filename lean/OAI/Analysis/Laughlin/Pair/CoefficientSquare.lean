import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

namespace Laughlin

theorem pairCoefficient_sq_choose (Q p : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    (pairCoefficient Q p x y)^2 =
      if x.val+y.val = p+1 then
        (((x.val : ℝ)-(y.val : ℝ))^2 * (Q.choose x.val : ℝ) * (Q.choose y.val : ℝ)) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
      else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs with h
  · rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  · simp

end Laughlin

end OAI

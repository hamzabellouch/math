import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Ostmann.Dirichlet

theorem contour_polynomial_budget (C D q T N : ℝ) (hC : 0<C) (hD : 0<D)
    (hq : 1 ≤ q) (hT : 2 ≤ T) (hN0 : 0 ≤ N) (hN : N ≤ D*q*(T+4)^4) :
    C*q*(T+7)*(1+16*(N+1)) ≤ (3*C*(17+256*D))*(q*(T+2))^5 := by
  let R : ℝ := q*(T+2)
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hT0 : 0 ≤ T+2 := by linarith
  have hR : 1 ≤ R := by
    dsimp [R]
    calc
      1 = 1*1 := by norm_num
      _ ≤ q*(T+2) := mul_le_mul hq (by linarith) (by norm_num) hq0
  have hq3 : 1 ≤ q^3 := one_le_pow₀ hq
  have hq4 : q ≤ q^4 := by
    have hm := mul_le_mul_of_nonneg_left hq3 hq0
    nlinarith only [hm]
  have hR4 : 1 ≤ R^4 := one_le_pow₀ hR
  have hshift : (T+4)^4 ≤ (2*(T+2))^4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hcount : N ≤ 16*D*R^4 := by
    calc
      N ≤ D*q*(T+4)^4 := hN
      _ ≤ D*q*(2*(T+2))^4 := mul_le_mul_of_nonneg_left hshift (mul_nonneg hD.le hq0)
      _ = (16*D*(T+2)^4)*q := by ring
      _ ≤ (16*D*(T+2)^4)*q^4 := mul_le_mul_of_nonneg_left hq4 (by positivity)
      _ = 16*D*R^4 := by dsimp [R]; ring
  have hbracket : 1+16*(N+1) ≤ (17+256*D)*R^4 := by
    nlinarith only [hcount,hR4]
  have hout : C*q*(T+7) ≤ 3*C*R := by
    calc
      C*q*(T+7) ≤ C*q*(3*(T+2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC.le hq0)
      _ = 3*C*R := by dsimp [R]; ring
  calc
    _ ≤ (3*C*R)*((17+256*D)*R^4) := mul_le_mul hout hbracket
      (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hC.le) (le_trans (by norm_num) hR))
    _ = _ := by dsimp [R]; ring

end Ostmann.Dirichlet

end OAI

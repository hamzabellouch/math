import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Cotype

theorem coefficient_numerical_contradiction {A B d : ℝ} (hd : 4 ≤ d)
    (hA : 80 * d * (d+1)^2 ≤ A) (hB : 80 * d * (d+1)^2 ≤ B)
    (hupper : A * B / 2 ≤ 4 * d * (d+1) * (A+B+10*d*(d+1)^2)) : False := by
  set t := d * (d+1) with htdef
  set u := d * (d+1)^2 with hudef
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hA' : 80 * u ≤ A := by nlinarith [hA]
  have hB' : 80 * u ≤ B := by nlinarith [hB]
  have hAn : 0 ≤ A := by linarith
  have hBn : 0 ≤ B := by linarith
  have hC : 0 < A+B := by linarith
  have hut : 5*t ≤ u := by
    have hh := mul_nonneg (show 0 ≤ d*(d+1) by positivity) (show 0 ≤ d-4 by linarith)
    dsimp [t, u]
    nlinarith [hh]
  have hp : 40*u*(A+B) ≤ A*B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA') hBn,
      mul_nonneg (sub_nonneg.mpr hB') hAn]
  have hs : 160*u ≤ A+B := by linarith
  have hlow : (17/4:ℝ)*t*(A+B) < 20*u*(A+B) := by
    nlinarith [mul_pos ht hC, mul_nonneg (sub_nonneg.mpr hut) hC.le]
  have hhigh : 4*t*(A+B+10*u) ≤ (17/4:ℝ)*t*(A+B) := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hs)]
  have hupper' : A*B/2 ≤ 4*t*(A+B+10*u) := by
    convert hupper using 1; dsimp [t, u]; ring
  linarith

end Cotype

end OAI

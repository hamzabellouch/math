import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z

@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]

theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]

theorem mul_lambda (z : ℝ) : z * lambda z = -Real.log (1 - z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [lambda_of_ne_zero hz]
    field_simp

theorem hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by
  by_cases hz : z = 0
  · subst z
    rw [lambda_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  · have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |z| < 1 by rwa [abs_of_nonneg hz0])).div_const z
    rw [lambda_of_ne_zero hz]
    convert hlog using 1
    ext j
    rw [pow_succ]
    field_simp

theorem summable_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) :=
  (hasSum_lambda hz0 hz1).summable

theorem monotoneOn_lambda : MonotoneOn lambda (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply hasSum_le _ (hasSum_lambda hx.1 hx.2) (hasSum_lambda hy.1 hy.2)
  intro j
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hxy j) (by positivity)

theorem one_le_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 1 ≤ lambda z := by
  simpa using monotoneOn_lambda (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hz0, hz1⟩ hz0

theorem lambda_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 ≤ lambda z :=
  zero_le_one.trans (one_le_lambda hz0 hz1)

end LeanBlast.CourtadeKumar

end

end OAI

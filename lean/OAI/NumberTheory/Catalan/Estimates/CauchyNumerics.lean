import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace InternalCatalan

theorem cauchy_radius_pos {n : ℕ} {r : ℝ} (hn : 48 ≤ n)
    (hr : 1 / (10 * (n : ℝ)) ≤ r) : 0 < r := by
  have hn48 : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  exact lt_of_lt_of_le (by positivity) hr

theorem cauchy_numerical_bound {n : ℕ} {r E : ℝ}
    (hn : 48 ≤ n) (hr : 1 / (10 * (n : ℝ)) ≤ r) (hE : 0 ≤ E) :
    (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * E / r ≤
      30 * E * (n : ℝ) := by
  have hn48 : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hrpos : 0 < r := cauchy_radius_pos hn hr
  have hpi : 3 / Real.pi ≤ 1 :=
    (div_le_iff₀ Real.pi_pos).mpr (by simpa only [one_mul] using Real.pi_gt_three.le)
  have hsmall : 2 / (n : ℝ) ≤ (1 : ℝ) / 2 :=
    (div_le_iff₀ hnpos).mpr (by linarith)
  have hlength : 2 * (1 + 2 / (n : ℝ)) ≤ 3 := by linarith
  have hcoefficient : (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) ≤ 3 := by
    calc
      _ ≤ 1 * (2 * (1 + 2 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
      _ ≤ 3 := by simpa only [one_mul] using hlength
  have hnr : 1 ≤ r * (10 * (n : ℝ)) :=
    (div_le_iff₀ (by positivity : 0 < 10 * (n : ℝ))).mp hr
  apply (div_le_iff₀ hrpos).mpr
  calc
    _ ≤ 3 * E := mul_le_mul_of_nonneg_right hcoefficient hE
    _ = (3 * E) * 1 := by ring
    _ ≤ (3 * E) * (r * (10 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hnr (mul_nonneg (by norm_num) hE)
    _ = (30 * E * (n : ℝ)) * r := by ring

theorem cauchy_exp_two_bound {n : ℕ} {r : ℝ}
    (hn : 48 ≤ n) (hr : 1 / (10 * (n : ℝ)) ≤ r) :
    (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / r ≤
      30 * Real.exp 2 * (n : ℝ) :=
  cauchy_numerical_bound hn hr (Real.exp_pos 2).le

end InternalCatalan

end OAI

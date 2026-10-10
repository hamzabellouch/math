import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Selection

theorem small_layer_coefficient_identity (m K : ℕ) (C D q : ℝ)
    (hm : 0 < m) (hK : 3 ≤ K) (hq : 0 < q) :
    (((Real.exp 1 * D * q / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) *
        (2 * C * (m : ℝ) / q) ^ ((K - 2) * m)) =
      ((6 * C * Real.exp 1 * D * (K : ℝ) ^ 2) *
        (2 * C * (m : ℝ) / q) ^ (K - 3)) ^ m := by
  have hmreal : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hshift : K - 2 = (K - 3) + 1 := by omega
  have hcancel :
      ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) =
        6 * C * Real.exp 1 * D * (K : ℝ) ^ 2 := by
    field_simp [hmreal.ne', hq.ne']
    ring
  have hbase :
      ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) ^ (K - 2) =
        (6 * C * Real.exp 1 * D * (K : ℝ) ^ 2) *
          (2 * C * (m : ℝ) / q) ^ (K - 3) := by
    rw [hshift, pow_succ (2 * C * (m : ℝ) / q) (K - 3)]
    calc
      _ = (((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
            (2 * C * (m : ℝ) / q)) *
            (2 * C * (m : ℝ) / q) ^ (K - 3) := by ring
      _ = _ := by rw [hcancel]
  calc
    _ = (((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) *
          (2 * C * (m : ℝ) / q) ^ (K - 2)) ^ m := by
      simp only [mul_pow, pow_mul]
    _ = _ := by rw [hbase]

theorem large_layer_count_le (m K : ℕ) (D q c1 : ℝ)
    (hm : 0 < m) (hD : 0 ≤ D) (hq : 0 < q) (hc1 : 0 < c1)
    (hlarge : c1 * q < (m : ℝ)) :
    (Real.exp 1 * D * q / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m ≤
      ((Real.exp 1 * D / c1) * 3 * (K : ℝ) ^ 2) ^ m := by
  have hmreal : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hDexp : 0 ≤ Real.exp 1 * D := mul_nonneg (Real.exp_pos 1).le hD
  have hratio0 : 0 ≤ Real.exp 1 * D * q / (m : ℝ) :=
    div_nonneg (mul_nonneg hDexp hq.le) hmreal.le
  have hcutoff0 : 0 ≤ Real.exp 1 * D / c1 := div_nonneg hDexp hc1.le
  have hratio : Real.exp 1 * D * q / (m : ℝ) ≤ Real.exp 1 * D / c1 := by
    apply (div_le_iff₀ hmreal).mpr
    calc
      Real.exp 1 * D * q = (Real.exp 1 * D / c1) * (c1 * q) := by
        field_simp [hc1.ne']

      _ ≤ (Real.exp 1 * D / c1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hlarge.le hcutoff0
  have hpool0 : 0 ≤ 3 * (K : ℝ) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hcoefficient :
      (Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2) ≤
        (Real.exp 1 * D / c1) * (3 * (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hratio hpool0
  calc
    _ = ((Real.exp 1 * D * q / (m : ℝ)) * (3 * (K : ℝ) ^ 2)) ^ m :=
      (mul_pow _ _ m).symm
    _ ≤ ((Real.exp 1 * D / c1) * (3 * (K : ℝ) ^ 2)) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hratio0 hpool0) hcoefficient m
    _ = _ := by rw [mul_assoc]

end RyserCoveringCounterexample.Selection

end OAI

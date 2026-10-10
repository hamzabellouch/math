import OAI.Combinatorics.ContingencyTables.Dense.DenseMixing

namespace OAI

/-! # Error budget of the bounded dense rejection schedule -/

namespace ContingencyTables.GridBoundary

theorem succ_le_two_pow (h : ℕ) : h + 1 ≤ 2 ^ h := by
  exact Nat.succ_le_of_lt Nat.lt_two_pow_self

theorem square_le_two_pow (d : ℕ) (hd : 4 ≤ d) : d ^ 2 ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    calc
      (d + 1) ^ 2 ≤ 2 * d ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ d := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

theorem dense_trial_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) ≤ (2 : ℝ) ^ (-(h : ℝ) - 2) := by
  have hd2 : (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ d := by exact_mod_cast square_le_two_pow d (by omega)
  have hd4 : (d : ℝ) ^ 4 ≤ (2 : ℝ) ^ (2 * d) := by
    calc
      _ = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) hd2 _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hh : (h : ℝ) + 1 ≤ (2 : ℝ) ^ h := by
    exact_mod_cast succ_le_two_pow h
  have hd1 : (1 : ℝ) + d ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (show 1 + d ≤ 2 ^ d by simpa only [Nat.add_comm] using succ_le_two_pow d)
  have hprod : ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((h : ℝ) + 3 * d) := by
    push_cast
    calc
      _ ≤ (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ h * (2 : ℝ) ^ d := by gcongr
      _ = _ := by
        rw [← pow_add, ← pow_add, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
  calc
    _ ≤ (2 : ℝ) ^ ((h : ℝ) + 3 * d) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = (2 : ℝ) ^ (-(3 * (h : ℝ) + d)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hd' : (14 : ℝ) ≤ d := by exact_mod_cast hd
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      linarith)

theorem dense_failure_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    (63 / 64 : ℝ) ^ (d ^ 4 * (h + 1)) ≤ (2 : ℝ) ^ (-(h : ℝ) - 2) := by
  have hd4 : 128 ≤ d ^ 4 := by nlinarith [show 14 ^ 4 ≤ d ^ 4 from Nat.pow_le_pow_left hd _]
  have hs : (63 / 64 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 64 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1 / 64 : ℝ))) ^ (d ^ 4 * (h + 1)) :=
      pow_le_pow_left₀ (by norm_num) hs _
    _ = Real.exp (-(((d ^ 4 * (h + 1) : ℕ) : ℝ) / 64)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(2 * ((h : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      have h' : (128 : ℝ) ≤ (d : ℝ) ^ 4 := by exact_mod_cast hd4
      push_cast
      nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
    _ ≤ (2 : ℝ) ^ (-(2 * ((h : ℝ) + 1))) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      nlinarith
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      linarith)

theorem dense_total_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    (63 / 64 : ℝ) ^ (d ^ 4 * (h + 1)) +
      ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) *
        (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  have hf := dense_failure_error_budget d h hd
  have ht := dense_trial_error_budget d h hd
  have heq : (2 : ℝ) ^ (-(h : ℝ) - 2) = (2 : ℝ) ^ (-(h : ℝ)) / 4 := by
    rw [Real.rpow_sub (by norm_num)]
    norm_num
  rw [heq] at hf ht
  linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(h : ℝ))]

end ContingencyTables.GridBoundary

end OAI

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.LineCover

private theorem log_one_quarter_le_neg_one : Real.log (1 / 4 : ℝ) ≤ -1 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.le_log_one_add_of_nonneg (x := 3) (by norm_num)
    norm_num at h
    linarith
  rw [one_div, Real.log_inv]
  linarith

theorem one_quarter_le_survival_pow_pred (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 1) := by
  have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqm : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hbase : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) := by
    field_simp [hq0.ne']
  have hb : (0 : ℝ) < 1 - 1 / (q : ℝ) := by
    rw [hbase]
    exact div_pos hqm hq0
  have hunit : ((q - 1 : ℕ) : ℝ) * (1 - (1 - 1 / (q : ℝ))⁻¹) = -1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one, hbase, inv_div]
    field_simp [hqm.ne']; ring
  have hlog := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hb)
    (Nat.cast_nonneg (q - 1) : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
  rw [hunit] at hlog
  apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1 / 4)
    (pow_pos hb (q - 1))).mp
  rw [Real.log_pow]
  exact log_one_quarter_le_neg_one.trans hlog

theorem one_quarter_le_survival_pow (q n : ℕ) (hq : 2 ≤ q) (hn : n ≤ q - 1) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ n := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hq0).2 (by linarith)
  have hb0 : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := sub_nonneg.mpr hinv
  have hb1 : 1 - 1 / (q : ℝ) ≤ 1 := by
    have hnonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := div_nonneg (by norm_num) hq0.le
    linarith
  exact (one_quarter_le_survival_pow_pred q hq).trans
    (pow_le_pow_of_le_one hb0 hb1 hn)

theorem one_quarter_le_survival_pow_sub_two (q : ℕ) (hq : 2 ≤ q) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ (q - 2) :=
  one_quarter_le_survival_pow q (q - 2) hq (Nat.sub_le_sub_left (by decide : 1 ≤ 2) q)

theorem quarter_mul_le_survival_mean (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) / 4 ≤ (q : ℝ) * (1 - 1 / (q : ℝ)) ^ (q - 2) := by
  have h := mul_le_mul_of_nonneg_left (one_quarter_le_survival_pow_sub_two q hq)
    (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  simpa only [mul_one_div] using h

end RyserCoveringCounterexample.LineCover

end OAI

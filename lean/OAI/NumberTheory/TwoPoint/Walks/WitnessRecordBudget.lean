import OAI.NumberTheory.TwoPoint.Walks.WitnessScaleParameters

namespace OAI

/-! One explicit polynomial budget covers all concatenated witness lengths and prime slots. -/

namespace TwoPointCorrelations

open Filter

/-- The bound includes the main length and number of witnesses as well as all prime slots. -/
def witnessRecordBudget (D J M n : ℕ) : ℕ := D * (J + M) + D + n

lemma witnessRecordBudget_length (D J M n : ℕ) : D ≤ witnessRecordBudget D J M n := by
  unfold witnessRecordBudget
  omega

lemma witnessRecordBudget_witnesses (D J M n : ℕ) : n ≤ witnessRecordBudget D J M n := by
  unfold witnessRecordBudget
  omega

lemma witnessRecordBudget_slots (D J M n r : ℕ) (hr : r ≤ D) :
    r * (J + M) ≤ witnessRecordBudget D J M n := by
  exact (Nat.mul_le_mul_right (J + M) hr).trans (by unfold witnessRecordBudget; omega)

lemma eventually_witnessRecordBudget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ D J M n : ℕ,
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      (n : ℝ) ≤ 4 * L → (witnessRecordBudget D J M n : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show 0 < 1 / (16 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (64 : ℝ), hsmall] with L hL hlog
  intro D J M n hD hJM hn
  have hLp : 0 < L := by linarith
  have hlogpos : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hlogpos, Real.norm_eq_abs,
    Real.rpow_one, abs_of_pos hLp] at hlog
  have hbudget : C * Real.log L ≤ L / 16 := by
    have hh : 16 * (C + 1) * Real.log L ≤ L := by
      have ht := hlog
      rw [one_div, inv_mul_eq_div] at ht
      simpa only [mul_comm] using
        (le_div_iff₀ (show 0 < 16 * (C + 1) by positivity)).mp ht
    nlinarith
  have hslots : (D : ℝ) * ((J + M : ℕ) : ℝ) ≤ L ^ (2 : ℕ) / 4 := by
    have hj : ((J + M : ℕ) : ℝ) ≤ L / 16 := hJM.trans hbudget
    have hm := mul_le_mul hD hj (Nat.cast_nonneg _) (by positivity : 0 ≤ 4 * L)
    nlinarith
  unfold witnessRecordBudget
  push_cast
  push_cast at hslots
  nlinarith

end TwoPointCorrelations

end OAI

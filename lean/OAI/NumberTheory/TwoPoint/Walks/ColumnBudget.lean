import OAI.NumberTheory.TwoPoint.Bounds.BoundedColumnCodes
import Mathlib.Data.Nat.Cast.Order.Field

namespace OAI

/-! The actual short-block budgets have the exponent required by the column code. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_short_block_floor :
    ∀ᶠ L : ℝ in atTop, L ^ (1 / 10 : ℝ) / 2 ≤ (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ∧
      0 < ⌊L ^ (1 / 10 : ℝ)⌋₊ := by
  have h := (tendsto_rpow_atTop (show 0 < (1 / 10 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [h] with L hL
  have hf := Nat.lt_floor_add_one (L ^ (1 / 10 : ℝ))
  have hp : (0 : ℝ) < (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by linarith
  exact ⟨by linarith, by exact_mod_cast hp⟩

/-- The two-half allowance is the final `+2` in the block count. All
remaining constants are absolute, and the exponent is exactly `0.92`. -/
theorem column_budget_bound (L : ℝ) (hL : 1 ≤ L)
    (n s imperfect omittedLabels blocks segments omittedRuns : ℕ)
    (hn : (n : ℝ) ≤ 2 * L)
    (hs : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hI : (imperfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ))
    (hO : (omittedLabels : ℝ) ≤ 2 * L ^ (1 / 50 : ℝ))
    (hB : blocks ≤ n / s + imperfect + 2)
    (hS : segments ≤ (omittedLabels + 1) * blocks)
    (hR : omittedRuns ≤ omittedLabels * blocks) :
    ((2 * segments + omittedRuns + imperfect : ℕ) : ℝ) ≤ 66 * L ^ (0.92 : ℝ) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hspos : (0 : ℝ) < s := (by positivity : (0 : ℝ) < L ^ (1 / 10 : ℝ) / 2).trans_le hs
  have hr : 1 ≤ L ^ (1 / 50 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hd : 1 ≤ L ^ (9 / 10 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hId : (imperfect : ℝ) ≤ 2 * L ^ (9 / 10 : ℝ) := hI.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (by norm_num))
  have hprod : L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hdiv : ((n / s : ℕ) : ℝ) ≤ 4 * L ^ (9 / 10 : ℝ) := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ hspos).mpr
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * L ^ (9 / 10 : ℝ) by positivity)
    calc
      (n : ℝ) ≤ 2 * L := hn
      _ = 2 * (L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ)) := by rw [hprod]
      _ = 4 * L ^ (9 / 10 : ℝ) * (L ^ (1 / 10 : ℝ) / 2) := by ring
      _ ≤ _ := hm
  have hB' : (blocks : ℝ) ≤ 8 * L ^ (9 / 10 : ℝ) := by
    have hb : (blocks : ℝ) ≤ ((n / s : ℕ) : ℝ) + imperfect + 2 := by exact_mod_cast hB
    linarith
  have hS' : (segments : ℝ) ≤ ((omittedLabels : ℝ) + 1) * blocks := by exact_mod_cast hS
  have hR' : (omittedRuns : ℝ) ≤ (omittedLabels : ℝ) * blocks := by exact_mod_cast hR
  have hfactor : 3 * (omittedLabels : ℝ) + 2 ≤ 8 * L ^ (1 / 50 : ℝ) := by linarith
  have hcost : (2 * (segments : ℝ) + omittedRuns + imperfect) ≤
      (3 * (omittedLabels : ℝ) + 2) * blocks + imperfect := by nlinarith
  have hm := mul_le_mul hfactor hB' (Nat.cast_nonneg blocks) (by positivity)
  have hI' : (imperfect : ℝ) ≤ 2 * (L ^ (1 / 50 : ℝ) * L ^ (9 / 10 : ℝ)) := by
    have ht := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hLp.le (9 / 10 : ℝ))
    nlinarith
  have hp : L ^ (1 / 50 : ℝ) * L ^ (9 / 10 : ℝ) = L ^ (0.92 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  push_cast
  nlinarith

end TwoPointCorrelations

end OAI

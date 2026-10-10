import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

noncomputable def spectatorBulkCount (k : ℕ) (L : ℝ) : ℕ :=
  2 * ⌊(k : ℝ) ^ 4 * L / 2⌋₊

theorem spectatorBulkCount_even (k : ℕ) (L : ℝ) : Even (spectatorBulkCount k L) := by
  exact ⟨⌊(k : ℝ) ^ 4 * L / 2⌋₊, by unfold spectatorBulkCount; omega⟩

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ)) atTop atTop := by
  have hk0 : 0 < (k : ℝ) ^ 4 := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) / (k : ℝ) ^ 4)] with L hL
  have h := (div_le_iff₀ hk0).mp hL
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_iteration_budget (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ) (hL : 1 ≤ L) (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (loss : ℕ → ℝ) (hloss : ∀ j < k, loss j ≤ L) :
    ∑ j ∈ Finset.range k, (loss j + Real.log 2) ≤ (spectatorBulkCount k L : ℝ) := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (4 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
    norm_num at h
    linarith
  have hk4 : 4 * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hk3 hk0]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  calc
    _ ≤ ∑ _j ∈ Finset.range k, (L + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact add_le_add (hloss j (Finset.mem_range.mp hj)) hlog
    _ = (k : ℝ) * (L + 1) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 2 * (k : ℝ) * L := by nlinarith
    _ ≤ (k : ℝ) ^ 4 * L / 2 := by nlinarith [mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)]
    _ ≤ _ := spectatorBulkCount_half k L hscale

end Ostmann

end OAI

import OAI.NumberTheory.JointDickman.Arithmetic.AdditionProgressionSieve

namespace OAI

/-! # A common interval for additions in a factor-four size window -/

namespace JointDickman
open Finset Classical

noncomputable def additionIntervalLower (W : ℝ) (j : ℕ) : ℕ := ⌊W/j⌋₊
noncomputable def additionIntervalUpper (W : ℝ) (j : ℕ) : ℕ := ⌊4*W/j⌋₊+1

theorem additionInterval_order {W : ℝ} {j : ℕ} (hW : 0 ≤ W) :
    additionIntervalLower W j ≤ additionIntervalUpper W j := by
  have hh : W/(j : ℝ) ≤ 4*W/j := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith
  exact (Nat.floor_mono hh).trans (Nat.le_succ _)

theorem additionInterval_contains {W : ℝ} {j z : ℕ} (hWz : W ≤ (z : ℝ))
    (hzW : (z : ℝ) ≤ 4*W) : z/j ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j) := by
  apply mem_Ico.mpr
  have hlo := Nat.floor_mono (div_le_div_of_nonneg_right hWz (Nat.cast_nonneg j))
  have hhi := Nat.floor_mono (div_le_div_of_nonneg_right hzW (Nat.cast_nonneg j))
  rw [Nat.floor_div_eq_div] at hlo hhi
  exact ⟨hlo,Nat.lt_succ_of_le hhi⟩

theorem additionInterval_denominator {W : ℝ} {j z₀ n : ℕ}
    (hj : 0 < j) (hW : 2*(j : ℝ) ≤ W)
    (hn : n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j)) :
    W/2 ≤ (z₀ : ℝ)+(j : ℝ)*n := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hf := Nat.lt_floor_add_one (W/(j : ℝ))
  change W/(j : ℝ) < (additionIntervalLower W j : ℝ)+1 at hf
  have hmul := (div_lt_iff₀ hjr).mp hf
  have hnr : (additionIntervalLower W j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
  have hz₀ : (0 : ℝ) ≤ z₀ := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hnr hjr.le]

theorem additionInterval_length {W : ℝ} {j : ℕ} (hj : 0 < j) (hW : (j : ℝ) ≤ W) :
    (additionIntervalUpper W j : ℝ)-additionIntervalLower W j ≤ 5*W/j := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 ≤ W := hjr.le.trans hW
  have hf := Nat.floor_le (div_nonneg (by linarith : 0 ≤ 4*W) hjr.le)
  have hlo : (0 : ℝ) ≤ additionIntervalLower W j := Nat.cast_nonneg _
  have hfrac : (1 : ℝ) ≤ W/j := (le_div_iff₀ hjr).mpr (by simpa using hW)
  dsimp only [additionIntervalUpper]
  push_cast
  linarith [show 5*W/j = 4*W/j+W/j by ring]

end JointDickman

end OAI

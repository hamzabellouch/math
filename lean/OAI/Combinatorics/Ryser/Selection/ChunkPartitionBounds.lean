import OAI.Combinatorics.Ryser.Selection.ChunkPartition
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Selection

theorem floor_chunkSize_pos (α q : ℝ) (hlarge : 2 ≤ α * q) :
    0 < Nat.floor (α * q) := by
  apply Nat.floor_pos.mpr
  linarith

theorem floor_chunkSize_le (α q : ℝ) (hα : 0 < α) (hq : 0 < q) :
    (Nat.floor (α * q) : ℝ) ≤ α * q :=
  Nat.floor_le (mul_pos hα hq).le

theorem floor_chunkSize_ge_half (α q : ℝ) (hlarge : 2 ≤ α * q) :
    α * q / 2 ≤ (Nat.floor (α * q) : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (α * q)
  linarith

variable {E : Type*} [instDecidableEqE : DecidableEq E]

theorem chunkCount_floor_le (T : Finset E) (α q D : ℝ)
    (hα : 0 < α) (hq : 0 < q) (hlarge : 2 ≤ α * q)
    (hT : (T.card : ℝ) ≤ 2 * D * q) (hD : 0 ≤ D) :
    (chunkCount T (Nat.floor (α * q)) : ℝ) ≤ 4 * D / α + 1 := let _ := instDecidableEqE; by
  have hfloorpos : 0 < (Nat.floor (α * q) : ℝ) :=
    Nat.cast_pos.mpr (floor_chunkSize_pos α q hlarge)
  have hhalfpos : 0 < α * q / 2 := div_pos (mul_pos hα hq) zero_lt_two
  have hnum : 0 ≤ 2 * D * q :=
    mul_nonneg (mul_nonneg (le_of_lt (zero_lt_two : (0 : ℝ) < 2)) hD) hq.le
  have hratio : (2 * D * q) / (α * q / 2) = 4 * D / α := by
    field_simp [ne_of_gt hα, ne_of_gt hq]
    ring
  calc
    (chunkCount T (Nat.floor (α * q)) : ℝ) =
        ((T.card / Nat.floor (α * q) : ℕ) : ℝ) + 1 := by
      simp only [chunkCount, Nat.cast_add, Nat.cast_one]
    _ ≤ (T.card : ℝ) / (Nat.floor (α * q) : ℝ) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right
          (Nat.cast_div_le (α := ℝ) (m := T.card) (n := Nat.floor (α * q))) (1 : ℝ))
    _ ≤ (2 * D * q) / (Nat.floor (α * q) : ℝ) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right (div_le_div_of_nonneg_right hT hfloorpos.le) (1 : ℝ))
    _ ≤ (2 * D * q) / (α * q / 2) + 1 := by
      simpa only [add_comm] using
        (add_le_add_right
          (div_le_div_of_nonneg_left hnum hhalfpos
            (floor_chunkSize_ge_half α q hlarge)) (1 : ℝ))
    _ = 4 * D / α + 1 := by rw [hratio]

theorem chunkCount_floor_le_nat (T : Finset E) (α q D : ℝ)
    (hα : 0 < α) (hq : 0 < q) (hlarge : 2 ≤ α * q)
    (hT : (T.card : ℝ) ≤ 2 * D * q) (hD : 0 ≤ D)
    (J : ℕ) (hJ : 4 * D / α + 1 ≤ (J : ℝ)) :
    chunkCount T (Nat.floor (α * q)) ≤ J := by
  exact Nat.cast_le.mp ((chunkCount_floor_le T α q D hα hq hlarge hT hD).trans hJ)

end RyserCoveringCounterexample.Selection

end OAI

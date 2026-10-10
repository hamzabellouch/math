import OAI.NumberTheory.Ostmann.Characters.AnchorNonbulkBudget
import OAI.NumberTheory.Ostmann.Characters.CharacterTargetGaps

namespace OAI

/-! # A depth-independent choice of the Section 4 diagonal gap constant -/
namespace Ostmann

/-- The bulk normalization costs `log 2 + log z`, while the prescribed gap
contains `20 log z`. The same choice of B works at every fixed depth. -/
theorem character_anchor_diagonal_small
    (B B₁ C z m gap energy prefactor : ℝ) (n : ℕ)
    (hz : 1 ≤ z) (hm : 0 ≤ m)
    (hB : 2 * B₁ + C + Real.log 2 + 6 ≤ B)
    (hgap : (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * m ≤ gap)
    (henergy : energy ≤ C * (2 ^ n : ℕ) * m)
    (hprefactor : prefactor ≤ Real.exp ((2 ^ n : ℕ) * m)) :
    Real.exp (-gap) * prefactor *
      Real.exp ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * m) := by
  have hrm : 0 ≤ (2 ^ n : ℕ) * m := mul_nonneg (Nat.cast_nonneg _) hm
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hb := mul_le_mul_of_nonneg_right hB hrm
  have hz' := mul_nonneg hlog hrm
  calc
    _ ≤ Real.exp (-gap) * Real.exp ((2 ^ n : ℕ) * m) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprefactor (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (-gap + (2 ^ n : ℕ) * m +
        ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Two independently bounded parts of the literal diagonal fit the one-unit
reserve in the amplitude recurrence. -/
theorem character_diagonal_sum_small (a b B m : ℝ) (n : ℕ) (hm : 1 ≤ m)
    (ha : a ≤ Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m))
    (hb : b ≤ Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m)) :
    a + b ≤ Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * m) := by
  have hr : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have hrm : 1 ≤ (2 ^ n : ℕ) * m := by nlinarith
  have htwo : 2 ≤ Real.exp ((2 ^ n : ℕ) * m) :=
    (by linarith : (2 : ℝ) ≤ (2 ^ n : ℕ) * m + 1).trans (Real.add_one_le_exp _)
  calc
    _ ≤ 2 * Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m) := by linarith
    _ ≤ Real.exp ((2 ^ n : ℕ) * m) * Real.exp (-(2 * B + 4) * (2 ^ n : ℕ) * m) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI

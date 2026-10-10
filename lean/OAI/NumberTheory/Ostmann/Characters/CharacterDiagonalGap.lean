import OAI.NumberTheory.Ostmann.Characters.CharacterIntervalGeometry
import OAI.NumberTheory.Ostmann.Characters.CharacterDiagonalBudget

namespace OAI

/-! # The original whole-word product pays the diagonal endpoint count -/
namespace Ostmann
open scoped Classical BigOperators

/-- Extract the reciprocal H product before summing the extended pivot.
The loss is only twice the fixed covering error. -/
theorem character_diagonal_product_gap {k n : ℕ} (hn : n < k)
    (J B z m F c : ℝ) (hc : 0 ≤ c) (a : Fin k → Bool → ℝ)
    (lo hi : CharacterRole k → ℕ)
    (hlo : ∀ i, Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i + c)) :
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let C := characterRangeError k c
    Real.exp (characterPivotGap B z m n - 2 * C) *
        (naturalProductCap (T ⟨n, hn⟩ + C) : ℝ) ≤
      ∏ h : CopyScheduleH (characterRole k) n, (lo (copyScheduleOrigin n h.val) : ℝ) := by
  intro T C
  let w := characterLogCenter J T a F
  have hp := (character_H_product_bounds hn w lo hi c hc hlo hhi).1
  change Real.exp (_ - C) ≤ _ at hp
  rw [← character_H_sum hn w, character_H_target_center hn J B z m F a] at hp
  rw [← Nat.cast_prod]
  apply le_trans _ hp
  calc
    _ ≤ Real.exp (characterPivotGap B z m n - 2 * C) * Real.exp (T ⟨n, hn⟩ + C) :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A fixed covering loss is absorbed by one unit of the linear gap coefficient. -/
theorem character_diagonal_gap_reserve (n : ℕ) (B z m C : ℝ)
    (hm : 0 ≤ m) (hC : 2 * C ≤ m) :
    (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * m ≤
      characterPivotGap B z m n - 2 * C := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hp hm
  have hs : 0 ≤ (4 : ℝ) ^ (n + 1) * Real.sqrt m := by positivity
  simp only [characterPivotGap, characterBaseGap, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

end Ostmann

end OAI

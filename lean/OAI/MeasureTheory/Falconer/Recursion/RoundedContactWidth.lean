import OAI.MeasureTheory.Falconer.Recursion.RoundedProfileContact

namespace OAI

/-! # Integer contact widths retain the real interval length up to one unit -/

namespace Falconer

theorem rounded_contact_width {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (N : ℕ) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (B-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B-A)*(N:ℝ)+1 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hab := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB hN)
  have haLo := Nat.floor_le (mul_nonneg hA hN)
  have hbLo := Nat.floor_le (mul_nonneg hB hN)
  have haHi := Nat.lt_floor_add_one (A*(N:ℝ))
  have hbHi := Nat.lt_floor_add_one (B*(N:ℝ))
  dsimp only
  rw [Nat.cast_sub hab]
  constructor <;> nlinarith

end Falconer

end OAI

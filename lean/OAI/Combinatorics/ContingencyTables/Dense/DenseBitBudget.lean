import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanStep
import OAI.Combinatorics.ContingencyTables.Transport.BoundedOffsetLaw

namespace OAI

/-! # Polynomial bounds for the manuscript's bounded dense random-bit budget -/

namespace ContingencyTables.GridBoundary

theorem denseStepBits_upper (d : ℕ) : denseStepBits d ≤ 16 * d ^ 5 := by
  have hl : Nat.clog 2 (8 * d) ≤ 8 * d :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hd : d ≤ d ^ 5 := Nat.le_self_pow (by decide) d
  unfold denseStepBits
  omega

theorem denseOffsetBits_upper (w C b h d : ℕ) (hw : w ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    FairBits.offsetBitLength w h d ≤ b + 1 + 4 * (h + d) := by
  have hl := (Nat.clog_mono_right 2 (by omega : w + 1 ≤ C + 2)).trans hb
  unfold FairBits.offsetBitLength
  omega

def denseRandomBitBudget (d b h : ℕ) : ℕ :=
  (d ^ 4 * (h + 1)) *
    ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d + d * (b + 1 + 4 * (h + d)))

/-- The fixed declared number of dense random bits is polynomial in the
dimension parameter, binary margin length, and requested precision. -/
theorem denseRandomBitBudget_polynomial (d b h : ℕ) :
    denseRandomBitBudget d b h ≤ 25 * (d + b + h + 1) ^ 62 := by
  let S := d + b + h + 1
  have hd : d ≤ S := by omega
  have hh : h + 1 ≤ S := by omega
  have hS : 1 ≤ S := by omega
  have hQ : denseStepBits d ≤ 16 * S ^ 5 :=
    (denseStepBits_upper d).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hd 5))
  have hH : d ^ 50 * (h + 1) ^ 2 ≤ S ^ 52 := by
    calc
      _ ≤ S ^ 50 * S ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd 50) (Nat.pow_le_pow_left hh 2)
      _ = _ := (pow_add S 50 2).symm
  have hwalk : (d ^ 50 * (h + 1) ^ 2) * denseStepBits d ≤ 16 * S ^ 57 := by
    calc
      _ ≤ S ^ 52 * (16 * S ^ 5) := Nat.mul_le_mul hH hQ
      _ = _ := by rw [mul_left_comm, ← pow_add]
  have hr : b + 1 + 4 * (h + d) ≤ 9 * S := by omega
  have hoffset : d * (b + 1 + 4 * (h + d)) ≤ 9 * S ^ 57 := by
    calc
      _ ≤ S * (9 * S) := Nat.mul_le_mul hd hr
      _ = 9 * S ^ 2 := by rw [mul_left_comm, pow_two]
      _ ≤ _ := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right hS (by decide : 2 ≤ 57))
  have hJ : d ^ 4 * (h + 1) ≤ S ^ 5 := by
    calc
      _ ≤ S ^ 4 * S := Nat.mul_le_mul (Nat.pow_le_pow_left hd 4) hh
      _ = _ := (pow_succ S 4).symm
  unfold denseRandomBitBudget
  calc
    _ ≤ S ^ 5 * (25 * S ^ 57) := Nat.mul_le_mul hJ (by omega)
    _ = _ := by rw [mul_left_comm, ← pow_add]

end ContingencyTables.GridBoundary

end OAI

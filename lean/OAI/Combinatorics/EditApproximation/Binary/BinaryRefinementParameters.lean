import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineParameters
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The decrement is constructed on the same Boolean words as the online
constants. In particular no rational literal or uncharged inversion is
needed at a local refinement entry. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem refinementDecrementWithWork_value (ell : List Bool) (hell : 0 < bitWordValue ell) :
    (refinementDecrementWithWork ell hell).1.value = 1 / (bitWordValue ell : ℚ) ^ 10 := by
  simp [refinementDecrementWithWork, value, SignedBinary.value, signedMagnitude,
    bitPowerWithWork_value, bitWordValue]

theorem refinementDecrementWithWork_width (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) : (refinementDecrementWithWork ell hell).1.width ≤ 10 * B + 1 := by
  have h := bitPowerWithWork_length_le ell 10 B hB
  simp only [refinementDecrementWithWork, width, List.length_cons, List.length_nil]
  exact max_le (by omega) h

theorem refinementDecrementWithWork_cost (ell : List Bool) (hell : 0 < bitWordValue ell)
    (B : ℕ) (hB : ell.length ≤ B) :
    (refinementDecrementWithWork ell hell).2 ≤ bitPowerBitBudget 10 B + 1 :=
  Nat.add_le_add_right (bitPowerWithWork_cost ell 10 B hB) 1

theorem refinementDecrementWithWork_cap (ell : List Bool) (hell : 0 < bitWordValue ell)
    (H : ℕ) (hH : 64 ≤ H) (hwidth : ell.length ≤ H) :
    (refinementDecrementWithWork ell hell).1.width ≤ H ^ 2 ∧
      (refinementDecrementWithWork ell hell).2 ≤ H ^ 8 := by
  constructor
  · exact (refinementDecrementWithWork_width ell hell H hwidth).trans (by nlinarith only [hH])
  · have h := refinementDecrementWithWork_cost ell hell H hwidth
    have hsmall : 11 * (H + 1) + 1 ≤ 12 * H := by omega
    have hsq := Nat.pow_le_pow_left hsmall 2
    have hnum : bitPowerBitBudget 10 H + 1 ≤ 300000 * H ^ 2 := by
      unfold bitPowerBitBudget
      nlinarith only [hsq, hH]
    have hc : 300000 ≤ H ^ 6 :=
      (by norm_num : 300000 ≤ (64 : ℕ) ^ 6).trans (Nat.pow_le_pow_left hH 6)
    exact h.trans (hnum.trans (by
      calc
        300000 * H ^ 2 ≤ H ^ 6 * H ^ 2 := Nat.mul_le_mul_right _ hc
        _ = H ^ 8 := by ring))

end BinaryFraction
end EditApproximation

end OAI

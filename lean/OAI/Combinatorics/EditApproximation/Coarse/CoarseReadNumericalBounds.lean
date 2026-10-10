import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadAccess
import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadLeafWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseNumericalUnit

namespace OAI

namespace EditApproximation

/-- The same small numerical envelope covers constructing a node's length. -/
theorem coarseDescriptorWithWork_height_bound (B d n offset H : ℕ)
    (hH : 10 ≤ H) (hd : d ≤ H) (hB : Nat.size B ≤ H ^ 3)
    (hn : Nat.size n ≤ H ^ 3) (ho : Nat.size offset ≤ H ^ 3) :
    (coarseDescriptorWithWork B d n offset).2 ≤ H ^ 30 := by
  have hc := coarseDescriptorWithWork_cost B d n offset (H ^ 3) hB hn ho
  have hp := BinaryFraction.bitPowerBitBudget_mono d H (H ^ 3) (7 * H ^ 3 + 3) hd (by omega)
  let W := 10 * (H + 2) * (H ^ 3 + 1) + 1
  have hw : (d + 2) * (H ^ 3 + 1) ≤ W := by
    have hm := Nat.mul_le_mul_right (H ^ 3 + 1) (show d + 2 ≤ H + 2 by omega)
    dsimp only [W]
    nlinarith only [hm, Nat.zero_le ((H + 2) * (H ^ 3 + 1))]
  have hl : 100 * (d + 2) * (H ^ 3 + 1) ≤ 1000 * W ^ 2 := by
    have hW : 1 ≤ W := by dsimp only [W]; omega
    nlinarith only [hw, hW]
  have hunit : (coarseDescriptorWithWork B d n offset).2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    change _ ≤ bitPowerBitBudget H (7 * H ^ 3 + 3) + 1000 * W ^ 2 + _
    omega
  exact hunit.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)

theorem coarseChildOffsetWithWork_height_bound (offset capacity index H : ℕ)
    (hH : 10 ≤ H) (ho : Nat.size offset ≤ H ^ 3)
    (hc : Nat.size capacity ≤ H ^ 3) (hi : Nat.size index ≤ H ^ 3) :
    (coarseChildOffsetWithWork offset capacity index).2 ≤ H ^ 30 := by
  have h := coarseChildOffsetWithWork_cost offset capacity index (H ^ 3) ho hc hi
  have hu : 200 * (H ^ 3 + 1) ^ 2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    omega
  exact h.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH))

theorem coarseReadShiftWithWork_height_bound (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) (H : ℕ)
    (hH : 10 ≤ H) (hk : Nat.size k ≤ H ^ 3) (hn : Nat.size n ≤ H ^ 3)
    (hs : Nat.size start ≤ H ^ 3) (hi : Nat.size shift.val ≤ H ^ 3)
    (ht : ∀ a ∈ target, Nat.size a ≤ H ^ 3)
    (hl : ∀ a, letter = some (some a) → Nat.size a ≤ H ^ 3) :
    (BinaryFraction.coarseReadShiftWithWork k n target letter start shift).2 ≤ H ^ 30 := by
  have h := BinaryFraction.coarseReadShiftWithWork_cost k n target letter start shift
    (H ^ 3) (H ^ 3) hk hn hs hi ht hl
  have hh : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hc : 200 * (H ^ 3 + 3) + 8 * H ^ 3 ≤ 100001000 * (H ^ 3 + 1) ^ 2 := by
    nlinarith only [hh]
  have hu : 100001000 * (H ^ 3 + 1) ^ 2 ≤ BinaryFraction.coarseNumericalUnit H := by
    unfold BinaryFraction.coarseNumericalUnit
    omega
  exact h.trans (hc.trans (hu.trans (BinaryFraction.coarseNumericalUnit_le_power H hH)))

end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilySampling
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling

namespace OAI

namespace EditApproximation

/-- The stream keeps the current word and one optional accepted value;
failed words are overwritten and the failure count belongs only to the
probability-space description, not to the machine state. -/
def rejectionStateCells (N bits : ℕ) (state : Option (Fin N)) (word : Fin (2 ^ bits)) : ℕ :=
  (state.map fun value => value.val.bits.length).getD 0 + word.val.bits.length + 4

theorem rejectionStateCells_bound (N bits : ℕ) (hN : N ≤ 2 ^ bits)
    (state : Option (Fin N)) (word : Fin (2 ^ bits)) :
    rejectionStateCells N bits state word ≤ 2 * bits + 4 := by
  have hw : word.val.bits.length ≤ bits := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr word.isLt
  have hs : (state.map fun value => value.val.bits.length).getD 0 ≤ bits := by
    cases state with
    | none => exact Nat.zero_le _
    | some value =>
      change value.val.bits.length ≤ bits
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (value.isLt.trans_le hN)
  unfold rejectionStateCells
  omega

/-- This bound holds after every transition, regardless of how many
failed trials preceded it. -/
theorem rejectionTransition_cells (N bits : ℕ) (hN : N ≤ 2 ^ bits)
    (state : Option (Fin N)) (word nextWord : Fin (2 ^ bits)) :
    rejectionStateCells N bits (rejectionTransition N (2 ^ bits) state word) nextWord ≤ 2 * bits + 4 :=
  rejectionStateCells_bound N bits hN _ _

theorem computedFamilySampler_cells (source target : List ℕ) (N R : ℕ)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : ComputedFamilyScalarKey source target N R)
    (state : Option (Fin (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key)))
    (word : Fin (2 ^ rejectionBitCount (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key))) :
    rejectionStateCells _ _ state word ≤ 2 * inputHeight N + 4 := by
  have h := rejectionStateCells_bound _ _ (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _) state word
  have hb := computedFamilyRange_bits_le source target N R hMass key
  dsimp only [rejectionBitCount] at hb
  exact h.trans (by omega)

end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Binary.BinaryGuardSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryEnvelopeSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem binaryGridRoundAllocation_le_work (spacing position : ℕ) :
    binaryGridRoundAllocation spacing position ≤ (binaryGridRoundWithWork spacing position).2 := by
  have hd := binaryNaturalDivAllocation_le_work position spacing
  have hm := bitMulAllocation_le_work spacing.bits (binaryNaturalDivModWithWork position spacing).1
  unfold binaryGridRoundAllocation binaryGridRoundWithWork
  dsimp only
  omega



theorem roundStateAllocation_le_work {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing) (q : TargetInterval n) :
    roundStateAllocation spacing q ≤ (roundStateWithWork spacing hspacing q).2 := by
  have hl := binaryGridRoundAllocation_le_work spacing q.lo
  have hr := binaryGridRoundAllocation_le_work spacing q.hi
  unfold roundStateAllocation roundStateWithWork binaryIntervalRoundWithWork
  dsimp only
  omega



theorem actionEqualAllocation_le_work {n M : ℕ} (a b : Fin M → TargetInterval n) :
    actionEqualAllocation a b ≤ (actionEqualWithWork a b).2 := by
  apply allAllocation_le_work
  intro i _
  have hl := naturalEqualAllocation_le_work (a i).lo (b i).lo
  have hr := naturalEqualAllocation_le_work (a i).hi (b i).hi
  dsimp only
  omega



theorem actionMemberAllocation_le_work {n M : ℕ} (a : Fin M → TargetInterval n)
    (actions : List (Fin M → TargetInterval n)) :
    actionMemberAllocation a actions ≤ (actionMemberWithWork a actions).2 := by
  induction actions with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have hh := actionEqualAllocation_le_work a b
    unfold actionMemberAllocation actionMemberWithWork
    dsimp only
    exact (Nat.add_le_add hh ih).trans (Nat.le_succ _)

namespace BinaryFraction



theorem roundedSpacingAllocation_le_work (theta envelope : BinaryFraction) :
    roundedSpacingAllocation theta envelope ≤ (roundedSpacingWithWork theta envelope).2 := by
  have hp := canonicalMulAllocation_le_work theta envelope
  have hm := maxAllocation_le_work one (canonicalMulWithWork theta envelope).1
  have hc := naturalCeilingAllocation_le_work (maxWithWork one (canonicalMulWithWork theta envelope).1).1
  unfold roundedSpacingAllocation roundedSpacingWithWork
  dsimp only
  omega



theorem roundedBandReadAllocation_le_work {n M : ℕ} (exponent b : ℕ) (band : List (Fin M → TargetInterval n))
    (hne : band ≠ []) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval n → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    roundedBandReadAllocation exponent b band hne read allocation ≤
      (roundedBandReadWithWork exponent b band hne read).2 := by
  apply vectorMapAllocation_le_work
  intro i
  have he := bandEnvelopeReadAllocation_le_work b band read allocation i (fun action _ => h i (action i))
  have hs := roundedSpacingAllocation_le_work (inversePowerTwo exponent) (bandEnvelopeReadWithWork b band read i).1
  have hr := roundStateAllocation_le_work
    (bitWordValue (roundedSpacingWithWork (inversePowerTwo exponent) (bandEnvelopeReadWithWork b band read i).1).1)
    (roundedSpacingWithWork_pos _ _) (band.head hne i)
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI

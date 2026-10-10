import OAI.Combinatorics.EditApproximation.Binary.BitAllocation
import OAI.Combinatorics.EditApproximation.Geometry.CanonicalFractionWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace SignedBinary

/-- Fresh magnitude cells in exactly the branch taken by signed addition. -/


theorem addAllocation_le_work (a b : SignedBinary) :
    a.addAllocation b ≤ (a.addWithWork b).2 := by
  have ha := bitAddAllocation_le_work a.bits b.bits false
  have hs := bitSubtractAllocation_le_work a.bits b.bits false
  have ht := bitSubtractAllocation_le_work b.bits a.bits false
  unfold addAllocation addWithWork
  split_ifs
  · dsimp only
    omega
  · cases h : (bitCompareWithWork a.bits b.bits).1 <;> simp only [h] <;> omega



theorem mulAllocation_le_work (a b : SignedBinary) :
    a.mulAllocation b ≤ (a.mulWithWork b).2 := by
  have h := bitMulAllocation_le_work a.bits b.bits
  change bitMulAllocation a.bits b.bits ≤ (bitMulWithWork a.bits b.bits).2 + 4
  omega

end SignedBinary
namespace BinaryFraction

/-- Counts every newly allocated magnitude and denominator cell, including
cross-products that are discarded after the numerator is computed. -/


theorem addAllocation_le_work (a b : BinaryFraction) :
    a.addAllocation b ≤ (a.addWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulAllocation_le_work b.numerator a.denominatorInteger
  have h3 := SignedBinary.addAllocation_le_work
    (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  have h4 := bitMulAllocation_le_work a.denominator b.denominator
  unfold addAllocation addWithWork
  dsimp only
  omega



theorem mulAllocation_le_work (a b : BinaryFraction) :
    a.mulAllocation b ≤ (a.mulWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.numerator
  have h2 := bitMulAllocation_le_work a.denominator b.denominator
  unfold mulAllocation mulWithWork
  dsimp only
  omega

/-- Signed comparisons themselves reuse input words; rational comparison
allocates just its two cross-products. -/


theorem ltAllocation_le_work (a b : BinaryFraction) :
    a.ltAllocation b ≤ (a.ltWithWork b).2 := by
  have h1 := SignedBinary.mulAllocation_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulAllocation_le_work b.numerator a.denominatorInteger
  unfold ltAllocation ltWithWork
  dsimp only
  omega



theorem canonicalizeAllocation_le_work (a : BinaryFraction) :
    canonicalizeAllocation a ≤ (canonicalizeWithWork a).2 := by
  have hn := trimBitWordAllocation_le_work a.numerator.bits
  have hd := trimBitWordAllocation_le_work a.denominator
  unfold canonicalizeAllocation canonicalizeWithWork
  dsimp only
  omega



theorem canonicalAddAllocation_le_work (a b : BinaryFraction) :
    canonicalAddAllocation a b ≤ (canonicalAddWithWork a b).2 := by
  exact Nat.add_le_add (addAllocation_le_work a b)
    (canonicalizeAllocation_le_work (a.addWithWork b).1)



theorem canonicalMulAllocation_le_work (a b : BinaryFraction) :
    canonicalMulAllocation a b ≤ (canonicalMulWithWork a b).2 := by
  exact Nat.add_le_add (mulAllocation_le_work a b)
    (canonicalizeAllocation_le_work (a.mulWithWork b).1)

end BinaryFraction
end EditApproximation

end OAI

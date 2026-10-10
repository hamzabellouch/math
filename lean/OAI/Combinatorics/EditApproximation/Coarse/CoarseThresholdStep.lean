import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdArithmetic
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGridInvariant
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Literal threshold numerator multiplication and denominator division.
The fixed-denominator quotient retains a root's common array grid. -/


private theorem coarseMultiply_nat_den (a : BinaryFraction) (n : ℕ) :
    (canonicalMulWithWork a (nat n)).1.representation.den = a.representation.den := by
  rw [canonicalMulWithWork_representation, nat_representation]
  simp only [UnreducedRational.mul, UnreducedRational.nat, mul_one]

 theorem coarseChildThresholdWithWork_value (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B)
    (hgrid : (coarseChildThreshold B q allowance.value draw).den ∣ allowance.representation.den) :
    (coarseChildThresholdWithWork B q allowance draw).1.value =
      coarseChildThreshold B q allowance.value draw := by
  unfold coarseChildThresholdWithWork
  dsimp only
  rw [coarseDivideWithWork_value]
  · simp only [canonicalMulWithWork_value, nat_value, coarseChildThreshold, Nat.cast_add,
      Nat.cast_one]
  · change Rat.den ((canonicalMulWithWork allowance (nat (draw.val + 1))).1.value /
      (canonicalMulWithWork (nat B) (nat q)).1.value) ∣
        (canonicalMulWithWork allowance (nat (draw.val + 1))).1.representation.den
    rw [coarseMultiply_nat_den]
    simpa only [canonicalMulWithWork_value, nat_value,
      coarseChildThreshold, Nat.cast_add, Nat.cast_one] using hgrid

 theorem coarseChildThresholdWithWork_den (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) :
    (coarseChildThresholdWithWork B q allowance draw).1.representation.den = allowance.representation.den := by
  exact (coarseDivideWithWork_den _ _).trans (coarseMultiply_nat_den allowance _)

/-- Local allowance division uses the same Boolean division and
compression primitive as threshold construction. -/


 theorem coarseChildAllowanceWithWork_value (L : ℕ) (threshold : BinaryFraction)
    (hgrid : (threshold.value / L).den ∣ threshold.representation.den) :
    (coarseChildAllowanceWithWork L threshold).1.value = threshold.value / L := by
  have hd : (threshold.value / (nat L).value).den ∣ bitWordValue threshold.denominator := by
    change (threshold.value / (nat L).value).den ∣ threshold.representation.den
    simpa only [nat_value] using hgrid
  simpa only [coarseChildAllowanceWithWork, nat_value] using
    coarseDivideWithWork_value threshold (nat L) hd

 theorem coarseChildAllowanceWithWork_den (L : ℕ) (threshold : BinaryFraction) :
    (coarseChildAllowanceWithWork L threshold).1.representation.den = threshold.representation.den :=
  coarseDivideWithWork_den _ _

end BinaryFraction
end EditApproximation

end OAI

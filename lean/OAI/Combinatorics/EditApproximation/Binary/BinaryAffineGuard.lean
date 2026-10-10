import OAI.Combinatorics.EditApproximation.Binary.BinaryDistanceWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Boolean tests for the affine errors in band membership.  The literal
product, both subtractions and final comparison have charged bit work. -/

namespace EditApproximation
namespace BinaryFraction

theorem canonicalMulWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.canonicalMulWithWork b).1.width ≤ 4 * B + 2 := by
  have hs := UnreducedRational.storageBits_mul a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := canonicalMulWithWork_self_width a b
  rw [canonicalMulWithWork_representation] at hw
  omega



@[simp] theorem affineErrorWithWork_value (position offset velocity prediction tolerance : BinaryFraction) :
    (affineErrorWithWork position offset velocity prediction tolerance).1 = true ↔
      |position.value - offset.value - velocity.value * prediction.value| ≤ tolerance.value := by
  simp only [affineErrorWithWork, leWithWork_value, absolute_value,
    subWithWork_value, canonicalMulWithWork_value]

def affineGuardBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 1 + 2000 * (B + 1) ^ 2 +
    (6000 * (12 * B + 9) ^ 2 + 1) +
    (1000 * (96 * B + 71) ^ 2 + 1) + 4

theorem affineErrorWithWork_cost (position offset velocity prediction tolerance : BinaryFraction)
    (B : ℕ) (hp : position.width ≤ B) (ho : offset.width ≤ B)
    (hv : velocity.width ≤ B) (hpred : prediction.width ≤ B) (ht : tolerance.width ≤ B) :
    (affineErrorWithWork position offset velocity prediction tolerance).2 ≤ affineGuardBitBudget B := by
  have hdw := subWithWork_width position offset B hp ho
  have hmw := canonicalMulWithWork_width velocity prediction B hv hpred
  have hd := subWithWork_cost position offset B hp ho
  have hm := canonicalMulWithWork_cost velocity prediction B hv hpred
  have hew := subWithWork_width (position.subWithWork offset).1
    (velocity.canonicalMulWithWork prediction).1 (12 * B + 8) (by omega) (by omega)
  have he := subWithWork_cost (position.subWithWork offset).1
    (velocity.canonicalMulWithWork prediction).1 (12 * B + 8) (by omega) (by omega)
  have hc := leWithWork_cost ((position.subWithWork offset).1.subWithWork
    (velocity.canonicalMulWithWork prediction).1).1.absolute tolerance (96 * B + 70)
    (by simpa only [absolute_width] using (hew.trans (by omega : 8 * (12 * B + 8) + 6 ≤ 96 * B + 70))) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at he hc
  change _ + _ + _ + _ + 4 ≤ _
  unfold affineGuardBitBudget
  omega

/-- Threshold used in every internal-cut predicate. -/


@[simp] theorem bandToleranceWithWork_value (tau theta : BinaryFraction) (b M : ℕ) :
    (bandToleranceWithWork tau theta b M).1.value = tau.value * theta.value * b / M := by
  simp only [bandToleranceWithWork, divWithWork_value, canonicalMulWithWork_value, nat_value]

theorem divWithWork_width_uniform (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.divWithWork b).1.width ≤ 4 * B + 4 := by
  have hs := UnreducedRational.storageBits_div a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := divWithWork_self_width a b
  rw [divWithWork_representation] at hw
  omega

def bandToleranceBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 2 * B + 3

theorem bandToleranceWithWork_bounds (tau theta : BinaryFraction) (b M B : ℕ)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B) :
    (bandToleranceWithWork tau theta b M).1.width ≤ 64 * B + 44 ∧
    (bandToleranceWithWork tau theta b M).2 ≤ bandToleranceBitBudget B := by
  have hpw := canonicalMulWithWork_width tau theta B htau htheta
  have hp := canonicalMulWithWork_cost tau theta B htau htheta
  have hsw := canonicalMulWithWork_width (canonicalMulWithWork tau theta).1 (nat b)
    (4 * B + 2) hpw ((nat_width_le b).trans (by omega))
  have hs := canonicalMulWithWork_cost (canonicalMulWithWork tau theta).1 (nat b)
    (4 * B + 2) hpw ((nat_width_le b).trans (by omega))
  have htw := divWithWork_width_uniform (canonicalMulWithWork
    (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M) (16 * B + 10)
    (by omega) ((nat_width_le M).trans (by omega))
  have ht := divWithWork_cost (canonicalMulWithWork
    (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M) (16 * B + 10)
    (by omega) ((nat_width_le M).trans (by omega))
  refine ⟨by dsimp only [bandToleranceWithWork]; omega, ?_⟩
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs ht
  change _ + _ + _ + Nat.size b + Nat.size M + 3 ≤ _
  unfold bandToleranceBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI

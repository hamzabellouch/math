import OAI.Combinatorics.EditApproximation.Numerics.ScalarControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdStep

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Control invocations of the shared-denominator scalar construction. -/
def coarseGridNatInvocations (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) : ℕ :=
  let raw : BinaryFraction :=
    ⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩
  bitMulInvocations n.bits denominator + canonicalizeInvocations raw + 1

theorem coarseGridNatInvocations_le_work (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    coarseGridNatInvocations denominator hden n ≤ (coarseGridNatWithWork denominator hden n).2 := by
  have hm := bitMulInvocations_le_work n.bits denominator
  have hc := canonicalizeInvocations_le_work
    (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩ : BinaryFraction)
  unfold coarseGridNatInvocations coarseGridNatWithWork
  dsimp only
  omega

def coarseGridAddInvocations (a b : BinaryFraction) : ℕ :=
  a.numerator.addInvocations b.numerator + canonicalizeInvocations
    ⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩ + 1

theorem coarseGridAddInvocations_le_work (a b : BinaryFraction) :
    coarseGridAddInvocations a b ≤ (coarseGridAddWithWork a b).2 := by
  have ha := SignedBinary.addInvocations_le_work a.numerator b.numerator
  have hc := canonicalizeInvocations_le_work
    ⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩
  unfold coarseGridAddInvocations coarseGridAddWithWork
  dsimp only
  omega

def coarseDivideInvocations (a divisor : BinaryFraction) : ℕ :=
  divInvocations a divisor +
    fixedDenominatorInvocations (divWithWork a divisor).1 a.denominator a.denominator_pos + 1

theorem coarseDivideInvocations_le_work (a divisor : BinaryFraction) :
    coarseDivideInvocations a divisor ≤ (coarseDivideWithWork a divisor).2 := by
  have hd := divInvocations_le_work a divisor
  have hf := fixedDenominatorInvocations_le_work (divWithWork a divisor).1
    a.denominator a.denominator_pos
  unfold coarseDivideInvocations coarseDivideWithWork
  dsimp only
  omega

def coarseContributionInvocations (threshold scale a : BinaryFraction) : ℕ :=
  (compareInvocations a threshold + 1) +
    (if (leWithWork threshold a).1 then (compareInvocations a scale + 1)
    else coarseGridNatInvocations a.denominator a.denominator_pos 0) + 1

theorem coarseContributionInvocations_le_work (threshold scale a : BinaryFraction) :
    coarseContributionInvocations threshold scale a ≤ (coarseContributionWithWork threshold scale a).2 := by
  have ht := compareInvocations_le_work a threshold
  have hm := compareInvocations_le_work a scale
  have hz := coarseGridNatInvocations_le_work a.denominator a.denominator_pos 0
  unfold coarseContributionInvocations coarseContributionWithWork
  dsimp only
  split_ifs <;> simp only [leWithWork, maxWithWork] <;> omega

/-- Includes a conservative allowance for the three literal constructors. -/
def coarseChildThresholdInvocations (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) : ℕ :=
  let numerator := canonicalMulWithWork allowance (nat (draw.val + 1))
  let divisor := canonicalMulWithWork (nat B) (nat q)
  canonicalMulInvocations allowance (nat (draw.val + 1)) +
    canonicalMulInvocations (nat B) (nat q) + coarseDivideInvocations numerator.1 divisor.1 +
    Nat.size (draw.val + 1) + Nat.size B + Nat.size q + 4

theorem coarseChildThresholdInvocations_le_work (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) :
    coarseChildThresholdInvocations B q allowance draw ≤
      (coarseChildThresholdWithWork B q allowance draw).2 := by
  have hn := canonicalMulInvocations_le_work allowance (nat (draw.val + 1))
  have hd := canonicalMulInvocations_le_work (nat B) (nat q)
  have hr := coarseDivideInvocations_le_work
    (canonicalMulWithWork allowance (nat (draw.val + 1))).1
    (canonicalMulWithWork (nat B) (nat q)).1
  unfold coarseChildThresholdInvocations coarseChildThresholdWithWork
  dsimp only
  omega

def coarseChildAllowanceInvocations (L : ℕ) (threshold : BinaryFraction) : ℕ :=
  coarseDivideInvocations threshold (nat L) + Nat.size L + 1

theorem coarseChildAllowanceInvocations_le_work (L : ℕ) (threshold : BinaryFraction) :
    coarseChildAllowanceInvocations L threshold ≤ (coarseChildAllowanceWithWork L threshold).2 := by
  have h := coarseDivideInvocations_le_work threshold (nat L)
  unfold coarseChildAllowanceInvocations coarseChildAllowanceWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI

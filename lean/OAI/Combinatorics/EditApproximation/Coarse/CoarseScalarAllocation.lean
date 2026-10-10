import OAI.Combinatorics.EditApproximation.Numerics.ScalarAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdStep

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Arithmetic-only allocation; the caller owns the input words. -/
def coarseGridNatAllocation (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) : ℕ :=
  let raw : BinaryFraction :=
    ⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩
  bitMulAllocation n.bits denominator + canonicalizeAllocation raw

theorem coarseGridNatAllocation_le_work (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    coarseGridNatAllocation denominator hden n ≤ (coarseGridNatWithWork denominator hden n).2 := by
  have hm := bitMulAllocation_le_work n.bits denominator
  have hc := canonicalizeAllocation_le_work
    (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩ : BinaryFraction)
  unfold coarseGridNatAllocation coarseGridNatWithWork
  dsimp only
  omega

def coarseGridAddAllocation (a b : BinaryFraction) : ℕ :=
  a.numerator.addAllocation b.numerator + canonicalizeAllocation
    ⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩

theorem coarseGridAddAllocation_le_work (a b : BinaryFraction) :
    coarseGridAddAllocation a b ≤ (coarseGridAddWithWork a b).2 := by
  have ha := SignedBinary.addAllocation_le_work a.numerator b.numerator
  have hc := canonicalizeAllocation_le_work
    ⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩
  unfold coarseGridAddAllocation coarseGridAddWithWork
  dsimp only
  omega

def coarseDivideAllocation (a divisor : BinaryFraction) : ℕ :=
  divAllocation a divisor +
    fixedDenominatorAllocation (divWithWork a divisor).1 a.denominator a.denominator_pos

theorem coarseDivideAllocation_le_work (a divisor : BinaryFraction) :
    coarseDivideAllocation a divisor ≤ (coarseDivideWithWork a divisor).2 := by
  have hd := divAllocation_le_work a divisor
  have hf := fixedDenominatorAllocation_le_work (divWithWork a divisor).1
    a.denominator a.denominator_pos
  unfold coarseDivideAllocation coarseDivideWithWork
  dsimp only
  omega

def coarseContributionAllocation (threshold scale a : BinaryFraction) : ℕ :=
  a.ltAllocation threshold +
    if (leWithWork threshold a).1 then a.ltAllocation scale
    else coarseGridNatAllocation a.denominator a.denominator_pos 0

theorem coarseContributionAllocation_le_work (threshold scale a : BinaryFraction) :
    coarseContributionAllocation threshold scale a ≤ (coarseContributionWithWork threshold scale a).2 := by
  have ht := ltAllocation_le_work a threshold
  have hm := ltAllocation_le_work a scale
  have hz := coarseGridNatAllocation_le_work a.denominator a.denominator_pos 0
  unfold coarseContributionAllocation coarseContributionWithWork
  dsimp only
  split_ifs <;> simp only [leWithWork, maxWithWork] <;> omega

/-- Includes all three natural literal numerators and their unit denominators. -/
def coarseChildThresholdAllocation (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) : ℕ :=
  let numerator := canonicalMulWithWork allowance (nat (draw.val + 1))
  let divisor := canonicalMulWithWork (nat B) (nat q)
  canonicalMulAllocation allowance (nat (draw.val + 1)) +
    canonicalMulAllocation (nat B) (nat q) + coarseDivideAllocation numerator.1 divisor.1 +
    Nat.size (draw.val + 1) + Nat.size B + Nat.size q + 3

theorem coarseChildThresholdAllocation_le_work (B q : ℕ) (allowance : BinaryFraction) (draw : Fin B) :
    coarseChildThresholdAllocation B q allowance draw ≤
      (coarseChildThresholdWithWork B q allowance draw).2 := by
  have hn := canonicalMulAllocation_le_work allowance (nat (draw.val + 1))
  have hd := canonicalMulAllocation_le_work (nat B) (nat q)
  have hr := coarseDivideAllocation_le_work
    (canonicalMulWithWork allowance (nat (draw.val + 1))).1
    (canonicalMulWithWork (nat B) (nat q)).1
  unfold coarseChildThresholdAllocation coarseChildThresholdWithWork
  dsimp only
  omega

def coarseChildAllowanceAllocation (L : ℕ) (threshold : BinaryFraction) : ℕ :=
  coarseDivideAllocation threshold (nat L) + Nat.size L + 1

theorem coarseChildAllowanceAllocation_le_work (L : ℕ) (threshold : BinaryFraction) :
    coarseChildAllowanceAllocation L threshold ≤ (coarseChildAllowanceWithWork L threshold).2 := by
  have h := coarseDivideAllocation_le_work threshold (nat L)
  unfold coarseChildAllowanceAllocation coarseChildAllowanceWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI

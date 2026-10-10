import OAI.Combinatorics.EditApproximation.Binary.BitControlSpace

namespace OAI

namespace EditApproximation
namespace SignedBinary

def addInvocations (a b : SignedBinary) : ℕ :=
  if a.negative = b.negative then bitAddInvocations a.bits b.bits false + 1
  else bitCompareInvocations a.bits b.bits + 1 +
    match (bitCompareWithWork a.bits b.bits).1 with
    | .eq => 0
    | .lt => bitSubtractInvocations b.bits a.bits false
    | .gt => bitSubtractInvocations a.bits b.bits false

theorem addInvocations_le_work (a b : SignedBinary) :
    addInvocations a b ≤ (a.addWithWork b).2 := by
  have ha := bitAddInvocations_le_work a.bits b.bits false
  have hc := bitCompareInvocations_le_work a.bits b.bits
  have hs := bitSubtractInvocations_le_work a.bits b.bits false
  have ht := bitSubtractInvocations_le_work b.bits a.bits false
  unfold addInvocations addWithWork
  split_ifs
  · dsimp only
    omega
  · cases h : (bitCompareWithWork a.bits b.bits).1 <;> simp only [h] <;> omega

def mulInvocations (a b : SignedBinary) : ℕ := bitMulInvocations a.bits b.bits + 1

theorem mulInvocations_le_work (a b : SignedBinary) :
    mulInvocations a b ≤ (a.mulWithWork b).2 := by
  have h := bitMulInvocations_le_work a.bits b.bits
  change bitMulInvocations a.bits b.bits + 1 ≤ (bitMulWithWork a.bits b.bits).2 + 4
  omega

end SignedBinary
namespace BinaryFraction

def addInvocations (a b : BinaryFraction) : ℕ :=
  a.numerator.mulInvocations b.denominatorInteger +
    b.numerator.mulInvocations a.denominatorInteger +
    ((a.numerator.mulWithWork b.denominatorInteger).1.addInvocations
      (b.numerator.mulWithWork a.denominatorInteger).1) +
    bitMulInvocations a.denominator b.denominator + 1

theorem addInvocations_add_one_le_work (a b : BinaryFraction) :
    a.addInvocations b + 1 ≤ (a.addWithWork b).2 := by
  have h1 := SignedBinary.mulInvocations_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulInvocations_le_work b.numerator a.denominatorInteger
  have h3 := SignedBinary.addInvocations_le_work
    (a.numerator.mulWithWork b.denominatorInteger).1 (b.numerator.mulWithWork a.denominatorInteger).1
  have h4 := bitMulInvocations_le_work a.denominator b.denominator
  unfold addInvocations addWithWork
  dsimp only
  omega

def mulInvocations (a b : BinaryFraction) : ℕ :=
  a.numerator.mulInvocations b.numerator + bitMulInvocations a.denominator b.denominator + 1

theorem mulInvocations_add_one_le_work (a b : BinaryFraction) :
    a.mulInvocations b + 1 ≤ (a.mulWithWork b).2 := by
  have hn := SignedBinary.mulInvocations_le_work a.numerator b.numerator
  have hd := bitMulInvocations_le_work a.denominator b.denominator
  unfold mulInvocations mulWithWork
  dsimp only
  omega

/-- Signed comparison may compare both words with zero. Its total recursive
Boolean-comparison frames are bounded by the explicitly counted work. -/
def signedLtInvocations (a b : SignedBinary) : ℕ :=
  if a.negative then
    if b.negative then bitCompareInvocations b.bits a.bits + 1
    else bitCompareInvocations a.bits [] + bitCompareInvocations b.bits [] + 3
  else if b.negative then 1 else bitCompareInvocations a.bits b.bits + 1

theorem signedLtInvocations_le_work (a b : SignedBinary) :
    signedLtInvocations a b ≤ (a.ltWithWork b).2 := by
  have hab := bitCompareInvocations_le_work a.bits b.bits
  have hba := bitCompareInvocations_le_work b.bits a.bits
  have ha := bitCompareInvocations_le_work a.bits []
  have hb := bitCompareInvocations_le_work b.bits []
  cases hna : a.negative <;> cases hnb : b.negative <;>
    simp only [signedLtInvocations, SignedBinary.ltWithWork, hna, hnb,
      Bool.false_eq_true, ↓reduceIte, SignedBinary.nonzeroWithWork] <;> omega

/-- Actual fraction-comparison invocation count, including signed comparison. -/
def compareInvocations (a b : BinaryFraction) : ℕ :=
  a.numerator.mulInvocations b.denominatorInteger +
    b.numerator.mulInvocations a.denominatorInteger +
    signedLtInvocations (a.numerator.mulWithWork b.denominatorInteger).1
      (b.numerator.mulWithWork a.denominatorInteger).1 + 1

theorem compareInvocations_le_work (a b : BinaryFraction) :
    compareInvocations a b ≤ (a.ltWithWork b).2 := by
  have h1 := SignedBinary.mulInvocations_le_work a.numerator b.denominatorInteger
  have h2 := SignedBinary.mulInvocations_le_work b.numerator a.denominatorInteger
  have h3 := signedLtInvocations_le_work (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  unfold compareInvocations ltWithWork
  dsimp only
  omega

def canonicalizeInvocations (a : BinaryFraction) : ℕ :=
  trimBitWordInvocations a.numerator.bits + trimBitWordInvocations a.denominator + 1

theorem canonicalizeInvocations_le_work (a : BinaryFraction) :
    canonicalizeInvocations a ≤ (canonicalizeWithWork a).2 := by
  have hn := trimBitWordInvocations_le_work a.numerator.bits
  have hd := trimBitWordInvocations_le_work a.denominator
  unfold canonicalizeInvocations canonicalizeWithWork
  dsimp only
  omega

def canonicalAddInvocations (a b : BinaryFraction) : ℕ :=
  a.addInvocations b + canonicalizeInvocations (a.addWithWork b).1 + 1

theorem canonicalAddInvocations_le_work (a b : BinaryFraction) :
    canonicalAddInvocations a b ≤ (canonicalAddWithWork a b).2 := by
  have ha := addInvocations_add_one_le_work a b
  have hc := canonicalizeInvocations_le_work (a.addWithWork b).1
  unfold canonicalAddInvocations canonicalAddWithWork
  dsimp only
  omega

def canonicalMulInvocations (a b : BinaryFraction) : ℕ :=
  a.mulInvocations b + canonicalizeInvocations (a.mulWithWork b).1 + 1

theorem canonicalMulInvocations_le_work (a b : BinaryFraction) :
    canonicalMulInvocations a b ≤ (canonicalMulWithWork a b).2 := by
  have ha := mulInvocations_add_one_le_work a b
  have hc := canonicalizeInvocations_le_work (a.mulWithWork b).1
  unfold canonicalMulInvocations canonicalMulWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI

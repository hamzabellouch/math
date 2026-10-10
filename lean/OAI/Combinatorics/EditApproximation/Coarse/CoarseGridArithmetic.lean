import OAI.Combinatorics.EditApproximation.Binary.BinaryFixedDenominator
import OAI.Combinatorics.EditApproximation.Binary.BinaryFiniteLoops
import OAI.Combinatorics.EditApproximation.Coarse.CoarsePrecision
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact arithmetic on a shared coarse-array denominator. Addition touches
only the signed numerators and keeps the denominator, preventing denominator
growth across the child-array sums. All counters run Boolean primitives. -/

namespace EditApproximation
namespace BinaryFraction

/-- Store an integer on the common denominator by a literal bit product. -/


 theorem coarseGridNatWithWork_value (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.value = n := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  simp only [value, SignedBinary.value, signedMagnitude, Bool.false_eq_true, ↓reduceIte,
    bitMulWithWork_value, bitWordValue_bits]
  push_cast
  exact mul_div_cancel_right₀ _ (by exact_mod_cast hden.ne')

 theorem coarseGridNatWithWork_den (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n : ℕ) :
    (coarseGridNatWithWork denominator hden n).1.representation.den =
      bitWordValue denominator := by
  unfold coarseGridNatWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

 theorem coarseGridNatWithWork_cost (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (n B : ℕ)
    (hn : Nat.size n ≤ B) (hd : denominator.length ≤ B) :
    (coarseGridNatWithWork denominator hden n).2 ≤ 100 * (B + 1) ^ 2 := by
  have hc := bitMulWithWork_cost n.bits denominator
  have hl := bitMulWithWork_length n.bits denominator
  have hnb : n.bits.length ≤ B := by simpa only [← Nat.size_eq_bits_len] using hn
  have hw : (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator,
      hden⟩ : BinaryFraction).width ≤ 3 * B + 1 := by
    change max (bitMulWithWork n.bits denominator).1.length denominator.length ≤ _
    apply max_le <;> omega
  have ht := canonicalizeWithWork_cost
    (⟨⟨false, (bitMulWithWork n.bits denominator).1⟩, denominator, hden⟩ : BinaryFraction)
  have hp : (bitMulWithWork n.bits denominator).2 ≤ 40 * (B + 1) ^ 2 := by
    apply hc.trans
    have hm := Nat.mul_le_mul (show n.bits.length + 1 ≤ B + 1 by omega)
      (show n.bits.length + denominator.length + 1 ≤ 2 * (B + 1) by omega)
    nlinarith only [hm]
  change (bitMulWithWork n.bits denominator).2 + _ + 3 ≤ _
  nlinarith only [hp, ht, hw, Nat.zero_le B]

/-- Add two stored cells after their denominators have been made identical. -/


 theorem coarseGridAddWithWork_value (a b : BinaryFraction)
    (hden : bitWordValue a.denominator = bitWordValue b.denominator) :
    (coarseGridAddWithWork a b).1.value = a.value + b.value := by
  unfold coarseGridAddWithWork
  dsimp only
  rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  simp only [value, SignedBinary.addWithWork_value, Int.cast_add, ← hden]
  ring

 theorem coarseGridAddWithWork_den (a b : BinaryFraction) :
    (coarseGridAddWithWork a b).1.representation.den = a.representation.den := by
  unfold coarseGridAddWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

 theorem coarseGridAddWithWork_cost (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (coarseGridAddWithWork a b).2 ≤ 100 * (B + 1) := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hc := SignedBinary.addWithWork_cost a.numerator b.numerator
  have hl := SignedBinary.addWithWork_length a.numerator b.numerator
  have hw : (⟨(a.numerator.addWithWork b.numerator).1, a.denominator,
      a.denominator_pos⟩ : BinaryFraction).width ≤ B + 1 := by
    change max (a.numerator.addWithWork b.numerator).1.bits.length a.denominator.length ≤ _
    apply max_le <;> omega
  have ht := canonicalizeWithWork_cost
    (⟨(a.numerator.addWithWork b.numerator).1, a.denominator, a.denominator_pos⟩ : BinaryFraction)
  change (a.numerator.addWithWork b.numerator).2 + _ + 3 ≤ _
  omega

 theorem coarseGridAddWithWork_width (a b : BinaryFraction) (V B : ℕ)
    (hden : bitWordValue a.denominator = bitWordValue b.denominator)
    (hvalue : |a.value + b.value| ≤ V) (hbits : a.denominator.length ≤ B) :
    (coarseGridAddWithWork a b).1.width ≤ Nat.size V + 2 * B + 1 := by
  let answer := (coarseGridAddWithWork a b).1
  have hv : |answer.representation.value| ≤ V := by
    rw [representation_value]
    exact (coarseGridAddWithWork_value a b hden) ▸ hvalue
  have hd : Nat.size answer.representation.den ≤ B := by
    rw [coarseGridAddWithWork_den]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length a.denominator)).trans hbits
  have hs := UnreducedRational.storageBits_le answer.representation V B hv hd
  have hw : answer.width ≤ answer.representation.storageBits := by
    unfold answer coarseGridAddWithWork
    dsimp only
    rw [canonicalizeWithWork_representation]
    exact canonicalizeWithWork_width_le_storageBits _
  exact hw.trans hs

end BinaryFraction
end EditApproximation

end OAI

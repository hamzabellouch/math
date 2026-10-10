import OAI.Combinatorics.EditApproximation.Binary.BinaryDivisionWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryRawCost
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact cache-value compression to a prescribed denominator.  It performs
one Boolean multiplication and one Boolean long division, followed only by
leading-zero removal.  No rational gcd or reduced-rational conversion is used. -/

namespace EditApproximation
namespace BinaryFraction

theorem raw_den_dvd_scaled_num (a : BinaryFraction) (D : ℕ) (hD : a.value.den ∣ D) :
    bitWordValue a.denominator ∣ bitWordValue a.numerator.bits * D := by
  have hd : (a.representation.den : ℤ) ≠ 0 := by exact_mod_cast a.representation.den_pos.ne'
  obtain ⟨c, hn, hd'⟩ := Rat.num_den_mk (q := a.value) (n := a.representation.num)
    (d := (a.representation.den : ℤ)) hd (by
      rw [Rat.divInt_eq_div, Int.cast_natCast]
      exact (representation_value a).symm)
  obtain ⟨k, hk⟩ := hD
  have hi : (a.representation.den : ℤ) ∣ a.representation.num * (D : ℤ) := by
    refine ⟨a.value.num * k, ?_⟩
    rw [hn, hd', hk, Nat.cast_mul]
    ring
  have habs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hi)
  have hnum : a.representation.num.natAbs = bitWordValue a.numerator.bits := by
    cases h : a.numerator.negative <;> simp [representation, SignedBinary.value, signedMagnitude, h]
  change bitWordValue a.denominator ∣ (a.representation.num * (D : ℤ)).natAbs at habs
  simpa only [Int.natAbs_mul, Int.natAbs_natCast, hnum] using habs



theorem fixedDenominatorWithWork_value (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.value = a.value := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  have hdvd := raw_den_dvd_scaled_num a (bitWordValue denominator) hD
  have h := bitDivModWithWork_value a.denominator product.1 a.denominator_pos
  have hm : bitWordValue product.1 = bitWordValue a.numerator.bits * bitWordValue denominator :=
    bitMulWithWork_value _ _
  have hmod : bitWordValue quotient.2.1 = 0 := by
    have hz : bitWordValue product.1 % bitWordValue a.denominator = 0 := by
      rw [hm]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h.1, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hz
    simp only [Nat.mod_mod] at hz
    exact (Nat.mod_eq_of_lt h.2).symm.trans hz
  have hq : bitWordValue a.denominator * bitWordValue quotient.1 =
      bitWordValue a.numerator.bits * bitWordValue denominator := by
    have heq := h.1
    change bitWordValue product.1 = bitWordValue a.denominator * bitWordValue quotient.1 + bitWordValue quotient.2.1 at heq
    rw [hmod, Nat.add_zero] at heq
    exact heq.symm.trans hm
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hc : (canonicalizeWithWork raw).1.value = raw.value := by
    rw [← representation_value, canonicalizeWithWork_representation, representation_value]
  change (canonicalizeWithWork raw).1.value = a.value
  rw [hc]
  have hdQ : (bitWordValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.denominator_pos.ne'
  have hDQ : (bitWordValue denominator : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hqQ : (bitWordValue a.denominator : ℚ) * bitWordValue quotient.1 =
      (bitWordValue a.numerator.bits : ℚ) * bitWordValue denominator := by exact_mod_cast hq
  cases hs : a.numerator.negative <;>
    simp only [raw, value, SignedBinary.value, signedMagnitude, hs, Bool.false_eq_true,
      ↓reduceIte, Int.cast_natCast, Int.cast_neg] <;>
    apply (div_eq_div_iff hDQ hdQ).mpr <;> nlinarith only [hqQ]

theorem fixedDenominatorWithWork_den (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    (fixedDenominatorWithWork a denominator hden).1.representation.den = bitWordValue denominator := by
  unfold fixedDenominatorWithWork
  dsimp only
  rw [canonicalizeWithWork_representation]
  rfl

theorem fixedDenominatorWithWork_width (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (hD : a.value.den ∣ bitWordValue denominator)
    (V B : ℕ) (hv : |a.value| ≤ V) (hB : denominator.length ≤ B) :
    (fixedDenominatorWithWork a denominator hden).1.width ≤ Nat.size V + 2 * B + 1 := by
  let answer := (fixedDenominatorWithWork a denominator hden).1
  have hvalue : |answer.representation.value| ≤ V := by
    rw [representation_value]
    change |(fixedDenominatorWithWork a denominator hden).1.value| ≤ V
    rw [fixedDenominatorWithWork_value a denominator hden hD]
    exact hv
  have hbits : Nat.size answer.representation.den ≤ B := by
    rw [fixedDenominatorWithWork_den]
    exact (Nat.size_le.mpr (bitWordValue_lt_pow_length denominator)).trans hB
  have hstorage := UnreducedRational.storageBits_le answer.representation V B hvalue hbits
  have hwidth : answer.width ≤ answer.representation.storageBits := by
    unfold answer fixedDenominatorWithWork
    dsimp only
    rw [canonicalizeWithWork_width, canonicalizeWithWork_representation]
    unfold UnreducedRational.storageBits
    omega
  exact hwidth.trans hstorage

theorem fixedDenominatorWithWork_cost (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) (A B : ℕ)
    (ha : a.width ≤ A) (hB : denominator.length ≤ B) :
    (fixedDenominatorWithWork a denominator hden).2 ≤ 5000 * (A + B + 2) ^ 2 := by
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  have hn : a.numerator.bits.length ≤ A := (le_max_left _ _).trans ha
  have hd : a.denominator.length ≤ A := (le_max_right _ _).trans ha
  have hp := bitMulWithWork_cost a.numerator.bits denominator
  have hpl := bitMulWithWork_length a.numerator.bits denominator
  have hq := bitDivModWithWork_cost a.denominator product.1
  have hql := (bitDivModWithWork_lengths a.denominator product.1).1
  change product.1.length ≤ 2 * a.numerator.bits.length + denominator.length + 1 at hpl
  change quotient.1.length = product.1.length at hql
  have hraw : raw.width ≤ 2 * A + B + 1 := by
    change max quotient.1.length denominator.length ≤ _
    exact max_le (by omega) (by omega)
  have hc := canonicalizeWithWork_cost raw
  change product.2 + quotient.2.2 + (canonicalizeWithWork raw).2 + 4 ≤ _
  have hprod : product.2 ≤ 20 * (A + B + 2) ^ 2 := by
    apply hp.trans
    have h1 : a.numerator.bits.length + 1 ≤ A + B + 2 := by omega
    have h2 : a.numerator.bits.length + denominator.length + 1 ≤ A + B + 2 := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  have hquot : quotient.2.2 ≤ 30 * (3 * (A + B + 2)) * (4 * (A + B + 2)) := by
    apply hq.trans
    have h1 : product.1.length + 1 ≤ 3 * (A + B + 2) := by omega
    have h2 : product.1.length + a.denominator.length + 1 ≤ 4 * (A + B + 2) := by omega
    nlinarith only [Nat.mul_le_mul h1 h2]
  nlinarith only [hprod, hquot, hc, hraw, Nat.zero_le A, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI

import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryMultiply
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalNormalize

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W03.BinaryMultiply

structure RatBits where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  deriving DecidableEq

def RatBits.length (x : RatBits) : ℕ := x.numerator.length + x.denominator.length + 1

def RatBits.magnitude (x : RatBits) : ℚ :=
  (bitsValue x.numerator : ℚ) / (bitsValue x.denominator : ℚ)

def RatBits.value (x : RatBits) : ℚ := if x.negative then -x.magnitude else x.magnitude

def normalize (x : RatBits) : RatBits :=
  let p := normalizeMagnitude x.numerator x.denominator
  ⟨if p.1 = [] then false else x.negative, p.1, p.2⟩

lemma normalizeMagnitude_value (num den : List Bool) :
    (bitsValue (normalizeMagnitude num den).1 : ℚ) /
      (bitsValue (normalizeMagnitude num den).2 : ℚ) =
      (bitsValue num : ℚ) / (bitsValue den : ℚ) := by
  let q := mkRat (bitsValue num : ℤ) (bitsValue den)
  have hq : q = (bitsValue num : ℚ) / (bitsValue den : ℚ) := by
    dsimp only [q]
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div]
    simp
  have hpos : 0 ≤ q := by rw [hq]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnum : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    have hi : (q.num.natAbs : ℤ) = q.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hpos)]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hi
  rw [normalizeMagnitude_correct]
  simp only [bitsValue_encodeNat]
  change (q.num.natAbs : ℚ) / q.den = _
  rw [hnum, Rat.num_div_den, hq]

@[simp] theorem normalize_value (x : RatBits) : (normalize x).value = x.value := by
  have hu := normalizeMagnitude_value x.numerator x.denominator
  by_cases hz : (normalizeMagnitude x.numerator x.denominator).1 = []
  · have hx : x.magnitude = 0 := by
      unfold RatBits.magnitude
      rw [← hu, hz]
      simp [bitsValue]
    change (bitsValue x.numerator : ℚ) / (bitsValue x.denominator : ℚ) = 0 at hx
    simp [normalize, RatBits.value, RatBits.magnitude, hz, bitsValue, hx]
  · cases hx : x.negative
    · simpa [normalize, RatBits.value, RatBits.magnitude, hz, hx] using hu
    · simpa [normalize, RatBits.value, RatBits.magnitude, hz, hx] using congrArg Neg.neg hu

def encodeMagnitude (q : ℚ) : RatBits :=
  ⟨decide (q.num < 0), Computability.encodeNat q.num.natAbs,
    Computability.encodeNat q.den⟩

def multiplyRat (x y : RatBits) : RatBits :=
  normalize ⟨Bool.xor x.negative y.negative,
    multiply x.numerator y.numerator, multiply x.denominator y.denominator⟩

def inverseRat (x : RatBits) : RatBits :=
  normalize ⟨x.negative, x.denominator, x.numerator⟩

theorem multiplyRat_value (x y : RatBits) : (multiplyRat x y).value = x.value * y.value := by
  rw [multiplyRat, normalize_value]
  cases hx : x.negative <;> cases hy : y.negative <;>
    simp [RatBits.value, RatBits.magnitude, hx, hy, multiply_correct, Nat.cast_mul,
      div_mul_div_comm]

theorem inverseRat_value (x : RatBits) : (inverseRat x).value = x.value⁻¹ := by
  rw [inverseRat, normalize_value]
  cases hx : x.negative <;> simp [RatBits.value, RatBits.magnitude, hx, inv_div]

def multiplyRatWork (x y : RatBits) : ℕ :=
  multiplyVisits x.numerator y.numerator + multiplyVisits x.denominator y.denominator +
    normalizeMagnitudeWork (multiply x.numerator y.numerator)
      (multiply x.denominator y.denominator) + 2

def inverseRatWork (x : RatBits) : ℕ :=
  normalizeMagnitudeWork x.denominator x.numerator + 2

theorem multiplyRatWork_polynomial (x y : RatBits) :
    multiplyRatWork x y ≤ 80 * (x.length + y.length + 2) ^ 3 := by
  let L := x.length + y.length
  have hnum : x.numerator.length + y.numerator.length ≤ L := by dsimp [L, RatBits.length]; omega
  have hden : x.denominator.length + y.denominator.length ≤ L := by dsimp [L, RatBits.length]; omega
  have hcombined : (multiply x.numerator y.numerator).length +
      (multiply x.denominator y.denominator).length ≤ L := by
    have hn := multiply_length_le x.numerator y.numerator
    have hd := multiply_length_le x.denominator y.denominator
    dsimp [L, RatBits.length]
    omega
  have h1 := (multiplyVisits_le x.numerator y.numerator).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hnum 2) 2)
  have h2 := (multiplyVisits_le x.denominator y.denominator).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hden 2) 2)
  have h3 := (normalizeMagnitudeWork_cubic (multiply x.numerator y.numerator)
    (multiply x.denominator y.denominator)).trans
    (Nat.mul_le_mul_left 70 (Nat.pow_le_pow_left (Nat.add_le_add_right hcombined 1) 3))
  unfold multiplyRatWork
  change _ ≤ 80 * (L + 2) ^ 3
  nlinarith

theorem inverseRatWork_polynomial (x : RatBits) :
    inverseRatWork x ≤ 72 * (x.length + 1) ^ 3 := by
  have h := normalizeMagnitudeWork_cubic x.denominator x.numerator
  have hbase : x.denominator.length + x.numerator.length + 1 ≤ x.length + 1 := by
    dsimp [RatBits.length]
    omega
  have hbound : normalizeMagnitudeWork x.denominator x.numerator ≤
      70 * (x.length + 1) ^ 3 := h.trans
    (Nat.mul_le_mul_left 70 (Nat.pow_le_pow_left hbase 3))
  have hpos : 0 < (x.length + 1) ^ 3 := Nat.pow_pos (by omega)
  unfold inverseRatWork
  omega

end KS.W30.BinaryRational

end

end OAI

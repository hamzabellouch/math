import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalCore

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W03.BinaryMultiply KS.W01.BinaryAdder

def signedValue (negative : Bool) (xs : List Bool) : ℤ :=
  if negative then -(bitsValue xs : ℤ) else (bitsValue xs : ℤ)

def addSigned (sx : Bool) (xs : List Bool) (sy : Bool) (ys : List Bool) :
    Bool × List Bool :=
  if sx = sy then (sx, trimBits (addBits false xs ys)) else
  if compareBits xs ys = .lt then (sy, trimBits (subtractBits ys xs false)) else
    (sx, trimBits (subtractBits xs ys false))

theorem addSigned_value (sx : Bool) (xs : List Bool) (sy : Bool) (ys : List Bool) :
    signedValue (addSigned sx xs sy ys).1 (addSigned sx xs sy ys).2 =
      signedValue sx xs + signedValue sy ys := by
  by_cases hs : sx = sy
  · subst sy
    have ha : (bitsValue (addBits false xs ys) : ℤ) =
        (bitsValue xs : ℤ) + bitsValue ys := by
      exact_mod_cast (by simpa using addBits_correct false xs ys :
        bitsValue (addBits false xs ys) = bitsValue xs + bitsValue ys)
    cases sx <;> simp [addSigned, signedValue, trimBits_value, ha]
    omega
  · by_cases hc : compareBits xs ys = .lt
    · have hlt := (compareBits_lt_iff xs ys).mp hc
      have he := subtractBits_correct ys xs false (by simpa using Nat.le_of_lt hlt)
      have hi : (bitsValue (subtractBits ys xs false) : ℤ) + bitsValue xs = bitsValue ys := by
        exact_mod_cast (by simpa using he :
          bitsValue (subtractBits ys xs false) + bitsValue xs = bitsValue ys)
      cases sx <;> cases sy <;> simp_all [addSigned, signedValue, trimBits_value] <;> omega
    · have hle : bitsValue ys ≤ bitsValue xs := by
        have hn : ¬bitsValue xs < bitsValue ys := fun h => hc ((compareBits_lt_iff xs ys).mpr h)
        omega
      have he := subtractBits_correct xs ys false (by simpa using hle)
      have hi : (bitsValue (subtractBits xs ys false) : ℤ) + bitsValue ys = bitsValue xs := by
        exact_mod_cast (by simpa using he :
          bitsValue (subtractBits xs ys false) + bitsValue ys = bitsValue xs)
      cases sx <;> cases sy <;> simp_all [addSigned, signedValue, trimBits_value] <;> omega

theorem addSigned_length (sx : Bool) (xs : List Bool) (sy : Bool) (ys : List Bool) :
    (addSigned sx xs sy ys).2.length ≤ max xs.length ys.length + 1 := by
  unfold addSigned
  split
  · exact (trimBits_length_le _).trans (addBits_length_le false xs ys)
  · split
    · have h := trimBits_length_le (subtractBits ys xs false)
      rw [subtractBits_length, max_comm] at h
      exact h.trans (Nat.le_succ _)
    · have h := trimBits_length_le (subtractBits xs ys false)
      rw [subtractBits_length] at h
      exact h.trans (Nat.le_succ _)

def addSignedWork (sx : Bool) (xs : List Bool) (sy : Bool) (ys : List Bool) : ℕ :=
  1 + if sx = sy then rippleVisits xs ys + trimBitCost (addBits false xs ys) else
    1 + bitScanCost xs ys + if compareBits xs ys = .lt then
      bitScanCost ys xs + trimBitCost (subtractBits ys xs false) else
      bitScanCost xs ys + trimBitCost (subtractBits xs ys false)

theorem addSignedWork_linear (sx : Bool) (xs : List Bool) (sy : Bool) (ys : List Bool) :
    addSignedWork sx xs sy ys ≤ 5 * (xs.length + ys.length + 1) := by
  have ha := addBits_length_le false xs ys
  unfold addSignedWork
  split
  · simp only [rippleVisits_eq, trimBitCost_eq]
    omega
  · split <;> simp only [bitScanCost_eq, trimBitCost_eq, subtractBits_length] <;> omega

def addRat (x y : RatBits) : RatBits :=
  let p := addSigned x.negative (multiply x.numerator y.denominator)
    y.negative (multiply y.numerator x.denominator)
  normalize ⟨p.1, p.2, multiply x.denominator y.denominator⟩

lemma value_eq_signed_div (x : RatBits) :
    x.value = (signedValue x.negative x.numerator : ℚ) / (bitsValue x.denominator : ℚ) := by
  cases hx : x.negative <;> simp [RatBits.value, RatBits.magnitude, signedValue, hx, neg_div]

lemma signedValue_multiply (s : Bool) (xs ys : List Bool) :
    signedValue s (multiply xs ys) = signedValue s xs * (bitsValue ys : ℤ) := by
  cases s <;> simp [signedValue, multiply_correct, Nat.cast_mul, neg_mul]

theorem addRat_value (x y : RatBits) (hx : bitsValue x.denominator ≠ 0)
    (hy : bitsValue y.denominator ≠ 0) : (addRat x y).value = x.value + y.value := by
  rw [addRat, normalize_value, value_eq_signed_div]
  simp only [addSigned_value, signedValue_multiply, multiply_correct, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [value_eq_signed_div x, value_eq_signed_div y]
  simpa only [mul_comm] using
    (div_add_div (signedValue x.negative x.numerator : ℚ)
      (signedValue y.negative y.numerator : ℚ)
      (Nat.cast_ne_zero.mpr hx) (Nat.cast_ne_zero.mpr hy)).symm

def addRatWork (x y : RatBits) : ℕ :=
  let a := multiply x.numerator y.denominator
  let b := multiply y.numerator x.denominator
  let p := addSigned x.negative a y.negative b
  multiplyVisits x.numerator y.denominator + multiplyVisits y.numerator x.denominator +
    multiplyVisits x.denominator y.denominator + addSignedWork x.negative a y.negative b +
    normalizeMagnitudeWork p.2 (multiply x.denominator y.denominator)

theorem addRatWork_polynomial (x y : RatBits) :
    addRatWork x y ≤ 1000 * (x.length + y.length + 2) ^ 3 := by
  let L := x.length + y.length
  have hn : x.numerator.length + y.denominator.length ≤ L := by dsimp [L, RatBits.length]; omega
  have hm : y.numerator.length + x.denominator.length ≤ L := by dsimp [L, RatBits.length]; omega
  have hd : x.denominator.length + y.denominator.length ≤ L := by dsimp [L, RatBits.length]; omega
  have ha := (multiply_length_le x.numerator y.denominator).trans hn
  have hb := (multiply_length_le y.numerator x.denominator).trans hm
  have hc := (multiply_length_le x.denominator y.denominator).trans hd
  have hp := addSigned_length x.negative (multiply x.numerator y.denominator)
    y.negative (multiply y.numerator x.denominator)
  have hp' : (addSigned x.negative (multiply x.numerator y.denominator)
      y.negative (multiply y.numerator x.denominator)).2.length ≤ L + 1 := by omega
  have w1 := (multiplyVisits_le x.numerator y.denominator).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 2) 2)
  have w2 := (multiplyVisits_le y.numerator x.denominator).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hm 2) 2)
  have w3 := (multiplyVisits_le x.denominator y.denominator).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hd 2) 2)
  have w4 := addSignedWork_linear x.negative (multiply x.numerator y.denominator)
    y.negative (multiply y.numerator x.denominator)
  have w5 := (normalizeMagnitudeWork_cubic
    (addSigned x.negative (multiply x.numerator y.denominator)
      y.negative (multiply y.numerator x.denominator)).2
    (multiply x.denominator y.denominator)).trans
      (Nat.mul_le_mul_left 70 (Nat.pow_le_pow_left (show
        (addSigned x.negative (multiply x.numerator y.denominator)
          y.negative (multiply y.numerator x.denominator)).2.length +
          (multiply x.denominator y.denominator).length + 1 ≤ 2 * (L + 1) by omega) 3))
  unfold addRatWork
  change _ ≤ 1000 * (L + 2) ^ 3
  nlinarith

end KS.W30.BinaryRational

end

end OAI

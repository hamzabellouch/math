import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdder
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

section

namespace KS.W01.WireMagnitude
open KS.W19

def decrement (xs : List Bool) : List Bool :=
  trimBits (subtractBits xs [true] false)

def increment (xs : List Bool) : List Bool :=
  trimBits (BinaryAdder.addBits true xs [])

theorem decrement_encode_succ (n : ℕ) :
    decrement (Computability.encodeNat (n + 1)) = Computability.encodeNat n := by
  have h := subtractBits_correct (Computability.encodeNat (n + 1)) [true] false
    (by simp [bitsValue, digit, bitsValue_encodeNat])
  have hv : bitsValue (subtractBits (Computability.encodeNat (n + 1)) [true] false) = n := by
    simp only [bitsValue_encodeNat, bitsValue, digit_true, digit_false] at h
    omega
  unfold decrement
  rw [trimBits_eq_encodeNat, hv]

theorem increment_encode (n : ℕ) :
    increment (Computability.encodeNat n) = Computability.encodeNat (n + 1) := by
  have h := BinaryAdder.addBits_correct true (Computability.encodeNat n) []
  have hv : bitsValue (BinaryAdder.addBits true (Computability.encodeNat n) []) = n + 1 := by
    simpa [bitsValue, digit, bitsValue_encodeNat] using h
  unfold increment
  rw [trimBits_eq_encodeNat, hv]

theorem decrement_length_le (xs : List Bool) :
    (decrement xs).length ≤ max xs.length 1 := by
  exact (trimBits_length_le _).trans_eq (by simp [subtractBits_length])

theorem increment_length_le (xs : List Bool) :
    (increment xs).length ≤ xs.length + 1 := by
  exact (trimBits_length_le _).trans (by
    simpa using BinaryAdder.addBits_length_le true xs [])

def constructorPayload (negative : Bool) (magnitude : List Bool) : List Bool :=
  if negative then decrement magnitude else trimBits magnitude

def magnitudePayload (negative : Bool) (constructor : List Bool) : List Bool :=
  if negative then increment constructor else trimBits constructor

def wireInt (negative : Bool) (magnitude : List Bool) : List Bool :=
  negative :: frame (constructorPayload negative magnitude)

theorem constructorPayload_encode (n : ℤ) :
    constructorPayload (decide (n < 0)) (Computability.encodeNat n.natAbs) =
      Computability.encodeNat (intPayload n) := by
  cases n with
  | ofNat n =>
      simp [constructorPayload, intPayload, trimBits_eq_encodeNat, bitsValue_encodeNat]
  | negSucc n =>
      simpa [constructorPayload, intPayload] using decrement_encode_succ n

theorem magnitudePayload_encode (n : ℤ) :
    magnitudePayload (decide (n < 0)) (Computability.encodeNat (intPayload n)) =
      Computability.encodeNat n.natAbs := by
  cases n with
  | ofNat n =>
      simp [magnitudePayload, intPayload, trimBits_eq_encodeNat, bitsValue_encodeNat]
  | negSucc n =>
      simpa [magnitudePayload, intPayload] using increment_encode n

theorem wireInt_encode (n : ℤ) :
    wireInt (decide (n < 0)) (Computability.encodeNat n.natAbs) = encodeInt n := by
  unfold wireInt
  rw [constructorPayload_encode]
  cases n <;> simp [encodeInt, encodeNat, intPayload]

def wireRat (negative : Bool) (numerator denominator : List Bool) : List Bool :=
  wireInt negative numerator ++ frame (trimBits denominator)

theorem wireRat_encode (q : ℚ) :
    wireRat (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) = encodeRat q := by
  rw [wireRat, wireInt_encode]
  simp [encodeRat, encodeNat, trimBits_eq_encodeNat, bitsValue_encodeNat]

theorem readRat_wireRat_encode (q : ℚ) (tail : List Bool) :
    readRat (wireRat (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) ++ tail) = some (q, tail) := by
  rw [wireRat_encode, readRat_encode_append]

theorem constructorPayload_length_le (negative : Bool) (xs : List Bool) :
    (constructorPayload negative xs).length ≤ xs.length + 1 := by
  cases negative
  · exact (trimBits_length_le _).trans (Nat.le_succ _)
  · exact (decrement_length_le _).trans (by omega)

theorem wireRat_length_le (negative : Bool) (num den : List Bool) :
    (wireRat negative num den).length ≤ 2 * (num.length + den.length) + 5 := by
  have hn := constructorPayload_length_le negative num
  have hd := trimBits_length_le den
  simp only [wireRat, wireInt, List.length_append, List.length_cons, length_frame]
  omega

end KS.W01.WireMagnitude

end

end OAI

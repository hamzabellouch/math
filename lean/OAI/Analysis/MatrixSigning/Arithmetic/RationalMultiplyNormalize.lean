import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplyProducts
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareCorrectness
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeCorrect

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product productTicks parseTicks prepareProgram

  negativeBit constructorBits pairBits fields signedFraction)

def rawProduct (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    KS.W30.BinaryRational.RatBits :=
  ⟨sa ^^ sb, product na nb, product da db⟩

theorem rawProduct_value (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    (rawProduct sa na da sb nb db).value =
      signedFraction sa (KS.W19.bitsValue na) (KS.W19.bitsValue da) *
        signedFraction sb (KS.W19.bitsValue nb) (KS.W19.bitsValue db) := by
  cases sa <;> cases sb <;>
    simp [rawProduct, KS.W30.BinaryRational.RatBits.value,
      KS.W30.BinaryRational.RatBits.magnitude, product, KS.W19.bitsValue_encodeNat,
      signedFraction, Nat.cast_mul, div_mul_div_comm, neg_div]

def rawCanonicalProduct (q r : ℚ) : KS.W30.BinaryRational.RatBits :=
  rawProduct (negativeBit q.num) (magnitude (negativeBit q.num) (constructorBits q.num))
    (Computability.encodeNat q.den) (negativeBit r.num)
    (magnitude (negativeBit r.num) (constructorBits r.num)) (Computability.encodeNat r.den)

theorem rawCanonicalProduct_value (q r : ℚ) : (rawCanonicalProduct q r).value = q * r := by
  unfold rawCanonicalProduct
  rw [rawProduct_value, KS.W06.RationalCompare.magnitude_constructor_value,
    KS.W06.RationalCompare.magnitude_constructor_value,
    KS.W19.bitsValue_encodeNat, KS.W19.bitsValue_encodeNat,
    KS.W06.RationalCompare.signedFraction_num_den,
    KS.W06.RationalCompare.signedFraction_num_den]

def normalizeProgram : Program 13 :=
  compose (compose (compose prepareProgram productsProgram) cleanupProgram)
    KS.W30.RationalMagnitudeMachine.program

def payloadSize (na da nb db : List Bool) : Nat := na.length + da.length + nb.length + db.length

def normalizeTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Nat :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    (productTicks a b + productTicks da db) + cleanupTicks a da b db) +
      300 * (payloadSize na da nb db + 3) ^ 3

theorem normalized_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let q := (rawProduct sa (magnitude sa na) da sb (magnitude sb nb) db).value
    RunSpec normalizeProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (KS.W30.RationalMagnitudeMachine.state (Computability.encodeNat q.num.natAbs)
        (Computability.encodeNat q.den) (decide (q.num < 0)))
      (normalizeTicks sa na da sb nb db) := by
  dsimp only
  let a := magnitude sa na
  let b := magnitude sb nb
  let L := payloadSize na da nb db + 2
  have hla := KS.W06.RationalCompare.magnitude_length_le sa na
  have hlb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hn : (product a b).length ≤ L := by
    have h := KS.W06.RationalCompare.product_length_le a b
    dsimp [a,b,L,payloadSize] at *
    omega
  have hd : (product da db).length ≤ L := by
    have h := KS.W06.RationalCompare.product_length_le da db
    dsimp [L,payloadSize]
    omega
  have hnorm := KS.W30.RationalMagnitudeMachine.normalizes_to_rational_encoding
    (rawProduct sa a da sb b db) L
    (KS.W19.canonicalBits_encodeNat _) (KS.W19.canonicalBits_encodeNat _) hn hd
  have h := (((KS.W06.RationalCompare.prepare_spec sa na da sb nb db).compose
    (products_spec sa a da sb b db)).compose (cleanup_spec sa a da sb b db)).compose hnorm
  exact h

def canonicalNormalizeTicks (q r : ℚ) : Nat :=
  normalizeTicks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)

theorem canonical_normalized_spec (q r : ℚ) :
    RunSpec normalizeProgram
      (fields (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [] [] [] [] [] [])
      (KS.W30.RationalMagnitudeMachine.state (Computability.encodeNat (q * r).num.natAbs)
        (Computability.encodeNat (q * r).den) (decide ((q * r).num < 0)))
      (canonicalNormalizeTicks q r) := by
  have h := normalized_spec (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den)
  change RunSpec normalizeProgram _
    (KS.W30.RationalMagnitudeMachine.state
      (Computability.encodeNat (rawCanonicalProduct q r).value.num.natAbs)
      (Computability.encodeNat (rawCanonicalProduct q r).value.den)
      (decide ((rawCanonicalProduct q r).value.num < 0))) _ at h
  rw [rawCanonicalProduct_value, KS.W06.RationalCompare.pairBits_encodeRat] at h
  exact h

theorem cleanupTicks_le (na da nb db : List Bool) :
    cleanupTicks na da nb db ≤ 3 * (na.length + da.length + nb.length + db.length) + 7 := by
  have hn := KS.W06.RationalCompare.product_length_le na nb
  have hd := KS.W06.RationalCompare.product_length_le da db
  unfold cleanupTicks
  rw [KS.W03.MultiplicationLoop.advance_length, KS.W03.MultiplicationLoop.advance_length]
  omega

theorem normalizeTicks_le (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    normalizeTicks sa na da sb nb db ≤
      1024 * ((pairBits sa na da sb nb db).length + 1) ^ 3 := by
  let S := payloadSize na da nb db
  let N := (pairBits sa na da sb nb db).length + 1
  have hN : N = 2 * S + 7 := by
    dsimp [N,S,payloadSize]
    rw [KS.W06.RationalCompare.pairBits_length]
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hp := KS.W06.RationalCompare.productTicks_le (magnitude sa na) (magnitude sb nb)
  have hd := KS.W06.RationalCompare.productTicks_le da db
  have hc := cleanupTicks_le (magnitude sa na) da (magnitude sb nb) db
  have hpn : (magnitude sa na).length + (magnitude sb nb).length + 2 ≤ N := by
    dsimp [S,payloadSize] at hN
    omega
  have hdn : da.length + db.length + 2 ≤ N := by
    dsimp [S,payloadSize] at hN
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hpn 2))
  have hd' := hd.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hdn 2))
  have hn : S + 3 ≤ N := by omega
  have hn' := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hn 3)
  have hNsq : N ^ 2 ≤ N ^ 3 := by
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hNlin : N ≤ N ^ 3 := by
    calc
      N = N ^ 1 := by simp
      _ ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp [normalizeTicks,parseTicks,payloadSize]
  change _ ≤ 1024 * N ^ 3
  dsimp [S,payloadSize] at hN hn'
  omega

theorem canonicalNormalizeTicks_le (q r : ℚ) :
    canonicalNormalizeTicks q r ≤
      1024 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) ^ 3 := by
  simpa only [canonicalNormalizeTicks, KS.W06.RationalCompare.pairBits_encodeRat] using
    normalizeTicks_le (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)

end KS.W15.RationalMultiply

end OAI

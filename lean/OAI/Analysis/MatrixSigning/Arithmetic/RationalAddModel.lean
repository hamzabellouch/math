import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalAdd
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddPrimitives
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareCorrectness

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W19 KS.W30.BinaryRational

def signedNumerator (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) : Bool × List Bool :=
  if sa = sb then (sa, addResult xs ys)
  else if bitsValue xs ≤ bitsValue ys then
    (sb, Computability.encodeNat (bitsValue ys - bitsValue xs))
  else (sa, Computability.encodeNat (bitsValue xs - bitsValue ys))

theorem signedNumerator_value (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    signedValue (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 =
      signedValue sa xs + signedValue sb ys := by
  by_cases h : bitsValue xs ≤ bitsValue ys
  · cases sa <;> cases sb <;>
      simp [signedNumerator, signedValue, addResult, h, bitsValue_encodeNat] <;> omega
  · cases sa <;> cases sb <;>
      simp [signedNumerator, signedValue, addResult, h, bitsValue_encodeNat] <;> omega

theorem subtractResult_length_le (xs ys : List Bool) (hsub : bitsValue ys ≤ bitsValue xs) :
    (Computability.encodeNat (bitsValue xs - bitsValue ys)).length ≤ max xs.length ys.length := by
  have hv := subtractBits_correct xs ys false (by simpa only [digit_false, Nat.add_zero] using hsub)
  have he : bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
    simp only [digit_false, Nat.add_zero] at hv
    omega
  have h := trimBits_length_le (subtractBits xs ys false)
  rw [trimBits_eq_encodeNat, he, subtractBits_length] at h
  exact h

theorem signedNumerator_length_le (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    (signedNumerator sa xs sb ys).2.length ≤ max xs.length ys.length + 1 := by
  unfold signedNumerator
  split
  · exact addResult_length_le xs ys
  · split
    · dsimp only [Prod.snd]
      have h := subtractResult_length_le ys xs (by assumption)
      simp only [max_comm] at h
      omega
    · dsimp only [Prod.snd]
      have h := subtractResult_length_le xs ys (by omega)
      omega

theorem signedNumerator_canonical (sa : Bool) (xs : List Bool) (sb : Bool) (ys : List Bool) :
    CanonicalBits (signedNumerator sa xs sb ys).2 := by
  unfold signedNumerator
  split
  · exact addResult_canonical xs ys
  · split <;> exact canonicalBits_encodeNat _

def rawSum (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : RatBits :=
  let p := signedNumerator sa (KS.W06.RationalCompare.product na db)
    sb (KS.W06.RationalCompare.product nb da)
  ⟨p.1, p.2, KS.W06.RationalCompare.product da db⟩

theorem rawSum_value (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool)
    (hd : bitsValue da ≠ 0) (he : bitsValue db ≠ 0) :
    (rawSum sa na da sb nb db).value =
      (RatBits.mk sa na da).value + (RatBits.mk sb nb db).value := by
  rw [value_eq_signed_div]
  simp only [rawSum, signedNumerator_value, KS.W06.RationalCompare.product, bitsValue_encodeNat]
  have hs (s : Bool) (xs ys : List Bool) :
      signedValue s (Computability.encodeNat (bitsValue xs * bitsValue ys)) =
        signedValue s xs * (bitsValue ys : ℤ) := by
    cases s <;> simp [signedValue, bitsValue_encodeNat, Nat.cast_mul, neg_mul]
  simp only [hs, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [value_eq_signed_div, value_eq_signed_div]
  simpa only [mul_comm] using
    (div_add_div (signedValue sa na : ℚ) (signedValue sb nb : ℚ)
      (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr he)).symm

theorem rawSum_encoded_value (q r : ℚ) :
    (rawSum (KS.W06.RationalCompare.negativeBit q.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit q.num)
        (KS.W06.RationalCompare.constructorBits q.num)) (Computability.encodeNat q.den)
      (KS.W06.RationalCompare.negativeBit r.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit r.num)
        (KS.W06.RationalCompare.constructorBits r.num)) (Computability.encodeNat r.den)).value = q + r := by
  rw [rawSum_value _ _ _ _ _ _ (by simpa only [bitsValue_encodeNat] using q.den_ne_zero)
    (by simpa only [bitsValue_encodeNat] using r.den_ne_zero)]
  have hq : (RatBits.mk (KS.W06.RationalCompare.negativeBit q.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit q.num)
        (KS.W06.RationalCompare.constructorBits q.num)) (Computability.encodeNat q.den)).value = q := by
    simpa [RatBits.value, RatBits.magnitude, KS.W06.RationalCompare.signedFraction,
      KS.W06.RationalCompare.magnitude_constructor_value, bitsValue_encodeNat, ite_div, neg_div] using
      KS.W06.RationalCompare.signedFraction_num_den q
  have hr : (RatBits.mk (KS.W06.RationalCompare.negativeBit r.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit r.num)
        (KS.W06.RationalCompare.constructorBits r.num)) (Computability.encodeNat r.den)).value = r := by
    simpa [RatBits.value, RatBits.magnitude, KS.W06.RationalCompare.signedFraction,
      KS.W06.RationalCompare.magnitude_constructor_value, bitsValue_encodeNat, ite_div, neg_div] using
      KS.W06.RationalCompare.signedFraction_num_den r
  rw [hq, hr]

end KS.W13.RationalAdd

end

end OAI

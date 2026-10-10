import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalAdd

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19

@[simp] theorem encodeMagnitude_value (q : ℚ) : (encodeMagnitude q).value = q := by
  have habs : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs q.num)
  by_cases hn : q.num < 0
  · have hn' : (q.num : ℚ) < 0 := by exact_mod_cast hn
    simp [encodeMagnitude, RatBits.value, RatBits.magnitude, bitsValue_encodeNat,
      hn, habs, abs_of_neg hn', neg_div, Rat.num_div_den]
  · have hn' : 0 ≤ (q.num : ℚ) := by exact_mod_cast (show 0 ≤ q.num by omega)
    simp [encodeMagnitude, RatBits.value, RatBits.magnitude, bitsValue_encodeNat,
      hn, habs, abs_of_nonneg hn', Rat.num_div_den]

theorem normalize_eq_encodeMagnitude (x : RatBits) :
    normalize x = encodeMagnitude x.value := by
  let q := mkRat (bitsValue x.numerator : ℤ) (bitsValue x.denominator)
  have hm : x.magnitude = q := by
    dsimp [RatBits.magnitude, q]
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div]
    simp
  have hq : 0 ≤ q.num := Rat.num_nonneg.mpr (by
    rw [← hm]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hc : normalizeMagnitude x.numerator x.denominator =
      (Computability.encodeNat q.num.natAbs, Computability.encodeNat q.den) :=
    normalizeMagnitude_correct _ _
  by_cases hz : q.num = 0
  · have hq0 : q = 0 := Rat.num_eq_zero.mp hz
    simp [normalize, hc, hq0, encodeMagnitude, RatBits.value, hm, Computability.encodeNat, Computability.encodeNum]
  · have hn : Computability.encodeNat q.num.natAbs ≠ [] := by
      intro he
      have hv := congrArg bitsValue he
      simp only [bitsValue_encodeNat, bitsValue] at hv
      exact hz (Int.natAbs_eq_zero.mp hv)
    have hp : 0 < q.num := by omega
    have hpq : 0 < q := Rat.num_pos.mp hp
    cases hx : x.negative <;>
      simp [normalize, hc, hn, encodeMagnitude, RatBits.value, hx, hm, hpq,
        show ¬q.num < 0 by omega]

@[simp] theorem multiplyRat_canonical (q r : ℚ) :
    multiplyRat (encodeMagnitude q) (encodeMagnitude r) = encodeMagnitude (q * r) := by
  have hv := multiplyRat_value (encodeMagnitude q) (encodeMagnitude r)
  rw [encodeMagnitude_value, encodeMagnitude_value] at hv
  unfold multiplyRat at hv ⊢
  rw [normalize_value] at hv
  rw [normalize_eq_encodeMagnitude, hv]

@[simp] theorem inverseRat_canonical (q : ℚ) :
    inverseRat (encodeMagnitude q) = encodeMagnitude q⁻¹ := by
  rw [inverseRat, normalize_eq_encodeMagnitude]
  have hv := inverseRat_value (encodeMagnitude q)
  rw [encodeMagnitude_value, inverseRat, normalize_value] at hv
  rw [hv]

@[simp] theorem addRat_canonical (q r : ℚ) :
    addRat (encodeMagnitude q) (encodeMagnitude r) = encodeMagnitude (q + r) := by
  have hx : bitsValue (encodeMagnitude q).denominator ≠ 0 := by
    simp [encodeMagnitude, bitsValue_encodeNat]
  have hy : bitsValue (encodeMagnitude r).denominator ≠ 0 := by
    simp [encodeMagnitude, bitsValue_encodeNat]
  have hv := addRat_value (encodeMagnitude q) (encodeMagnitude r) hx hy
  rw [encodeMagnitude_value, encodeMagnitude_value] at hv
  unfold addRat at hv ⊢
  rw [normalize_value] at hv
  rw [normalize_eq_encodeMagnitude, hv]

end KS.W30.BinaryRational

end

end OAI

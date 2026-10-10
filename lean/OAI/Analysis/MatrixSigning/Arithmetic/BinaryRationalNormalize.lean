import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryGCD
import OAI.Analysis.MatrixSigning.Complexity.BinaryGCDCost

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19 KS.W30.BinaryGCD

lemma quotient_value (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    bitsValue (divideBits ys xs).1 = bitsValue xs / bitsValue ys := by
  obtain ⟨he, hr⟩ := divideBits_correct ys xs hy
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith

def normalizeMagnitude (num den : List Bool) : List Bool × List Bool :=
  if trimBits den = [] then ([], [true]) else
  let g := gcdBits num den
  (trimBits (divideBits g num).1, trimBits (divideBits g den).1)

theorem normalizeMagnitude_correct (num den : List Bool) :
    let q := mkRat (bitsValue num : ℤ) (bitsValue den)
    normalizeMagnitude num den =
      (Computability.encodeNat q.num.natAbs, Computability.encodeNat q.den) := by
  by_cases hz : bitsValue den = 0
  · simp [normalizeMagnitude, (trim_eq_nil_iff den).mpr hz, hz, Computability.encodeNat,
      Computability.encodeNum, Computability.encodePosNum]
  · have hd : 0 < bitsValue den := Nat.pos_of_ne_zero hz
    have hg : 0 < bitsValue (gcdBits num den) := by
      rw [gcdBits_correct]
      exact Nat.gcd_pos_of_pos_right _ hd
    have hn : (mkRat (bitsValue num : ℤ) (bitsValue den)).num.natAbs =
        bitsValue num / Nat.gcd (bitsValue num) (bitsValue den) := by
      simp [Rat.num_mkRat, hz, ← Int.natCast_ediv, Nat.gcd_comm]
    have hd' : (mkRat (bitsValue num : ℤ) (bitsValue den)).den =
        bitsValue den / Nat.gcd (bitsValue num) (bitsValue den) := by
      simp [Rat.den_mkRat, hz, Nat.gcd_comm]
    have htrim : trimBits den ≠ [] := by simpa [trim_eq_nil_iff] using hz
    rw [normalizeMagnitude, ite_eq_right htrim]
    simp only [trimBits_eq_encodeNat, quotient_value _ _ hg, gcdBits_correct, hn, hd']

def normalizeMagnitudeWork (num den : List Bool) : ℕ :=
  trimBitCost den + 1 +
  if trimBits den = [] then 2 else
  let g := gcdBits num den
  gcdBitsWork num den + divisionBitCost g num + trimBitCost (divideBits g num).1 +
    divisionBitCost g den + trimBitCost (divideBits g den).1

theorem normalizeMagnitudeWork_cubic (num den : List Bool) :
    normalizeMagnitudeWork num den ≤ 70 * (num.length + den.length + 1) ^ 3 := by
  let L := num.length + den.length
  have hn : num.length ≤ L := by dsimp [L]; omega
  have hd : den.length ≤ L := by dsimp [L]; omega
  by_cases hz : trimBits den = []
  · simp only [normalizeMagnitudeWork, ite_eq_left hz, trimBitCost_eq]
    change den.length + 1 + 1 + 2 ≤ 70 * (L + 1) ^ 3
    have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
    omega
  · have hp : 0 < bitsValue den := by
      apply Nat.pos_of_ne_zero
      exact fun h => hz ((trim_eq_nil_iff den).mpr h)
    have hg : (gcdBits num den).length ≤ L := (gcdBits_length_le_right num den hp).trans hd
    have hc := gcdBitsWork_cubic num den
    have hnCost := division_cost_uniform num (gcdBits num den) hn hg
    have hdCost := division_cost_uniform den (gcdBits num den) hd hg
    simp only [normalizeMagnitudeWork, ite_eq_right hz, trimBitCost_eq, divideBits_quotient_length]
    change den.length + 1 + 1 + (gcdBitsWork num den +
      divisionBitCost (gcdBits num den) num + (num.length + 1) +
      divisionBitCost (gcdBits num den) den + (den.length + 1)) ≤ 70 * (L + 1) ^ 3
    change gcdBitsWork num den ≤ 41 * (L + 1) ^ 3 at hc
    nlinarith

theorem normalize_canonical_rational_work (q : ℚ) :
    normalizeMagnitudeWork (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) ≤
        70 * (Nat.size q.num.natAbs + Nat.size q.den + 1) ^ 3 := by
  simpa only [encodeNat_length_eq_size] using normalizeMagnitudeWork_cubic
    (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)

end KS.W30.BinaryRational

end

end OAI

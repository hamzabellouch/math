import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

section

namespace KS.W30.BinaryGCD
open KS.W19

lemma trimmed_remainder_length_le (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    (trimBits (divideBits ys xs).2).length ≤ ys.length := by
  apply trimBits_length_le_of_value_lt
  exact lt_trans (divideBits_correct ys xs hy).2 (bitsValue_lt_two_pow_length ys)

lemma division_cost_uniform {L : ℕ} (xs ys : List Bool)
    (hx : xs.length ≤ L) (hy : ys.length ≤ L) :
    divisionBitCost ys xs ≤ 6 * (L + 1) ^ 2 := by
  calc
    divisionBitCost ys xs ≤ xs.length * (xs.length + 4 * ys.length + 4) + 1 :=
      divisionBitCost_le ys xs
    _ ≤ L * (5 * L + 4) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul hx (by omega)) 1
    _ ≤ 6 * (L + 1) ^ 2 := by nlinarith

def gcdRoundsWork : ℕ → List Bool → List Bool → ℕ
  | 0, xs, _ys => trimBitCost xs
  | k + 1, xs, ys =>
      let v := trimBits ys
      trimBitCost ys + 1 +
      if v = [] then trimBitCost xs else
      let rawr := (divideBits v xs).2
      let r := trimBits rawr
      divisionBitCost v xs + trimBitCost rawr + 1 +
      if r = [] then 0 else
      let raws := (divideBits r v).2
      let s := trimBits raws
      divisionBitCost r v + trimBitCost raws + 1 + gcdRoundsWork k r s

theorem gcdRoundsWork_le (fuel L : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ L) (hy : ys.length ≤ L) :
    gcdRoundsWork fuel xs ys ≤ 20 * (fuel + 1) * (L + 1) ^ 2 := by
  induction fuel generalizing xs ys with
  | zero =>
      simp only [gcdRoundsWork, trimBitCost_eq]
      nlinarith
  | succ fuel ih =>
      let v := trimBits ys
      have hvlen : v.length ≤ L := (trimBits_length_le ys).trans hy
      by_cases hv : v = []
      · simp only [gcdRoundsWork, v, ite_eq_left hv, trimBitCost_eq]
        nlinarith [Nat.zero_le (fuel * (L + 1) ^ 2)]
      · have hvpos : 0 < bitsValue v := canonicalBits_value_pos v (trimBits_canonical ys) hv
        let rawr := (divideBits v xs).2
        let r := trimBits rawr
        have hrawr : rawr.length ≤ 2 * L := by
          have h := divideBits_remainder_length v xs
          dsimp [rawr]
          omega
        have hrlen : r.length ≤ L := (trimmed_remainder_length_le v xs hvpos).trans hvlen
        have hc1 := division_cost_uniform xs v hx hvlen
        by_cases hr : r = []
        · simp only [gcdRoundsWork, v, ite_eq_right hv, rawr, r, ite_eq_left hr, Nat.add_zero,
            trimBitCost_eq]
          nlinarith [Nat.zero_le (fuel * (L + 1) ^ 2)]
        · have hrpos : 0 < bitsValue r := canonicalBits_value_pos r (trimBits_canonical rawr) hr
          let raws := (divideBits r v).2
          let s := trimBits raws
          have hraws : raws.length ≤ 2 * L := by
            have h := divideBits_remainder_length r v
            dsimp [raws]
            omega
          have hslen : s.length ≤ L := (trimmed_remainder_length_le r v hrpos).trans hrlen
          have hc2 := division_cost_uniform v r hvlen hrlen
          have hi := ih r s hrlen hslen
          simp only [gcdRoundsWork, v, ite_eq_right hv, rawr, r, ite_eq_right hr,
            trimBitCost_eq]
          nlinarith

def gcdBitsWork (xs ys : List Bool) : ℕ :=
  ys.length + 1 + gcdRoundsWork (ys.length + 1) xs ys

theorem gcdBitsWork_cubic (xs ys : List Bool) :
    gcdBitsWork xs ys ≤ 41 * (xs.length + ys.length + 1) ^ 3 := by
  let L := xs.length + ys.length
  have hx : xs.length ≤ L := by dsimp [L]; omega
  have hy : ys.length ≤ L := by dsimp [L]; omega
  have h := gcdRoundsWork_le (ys.length + 1) L xs ys hx hy
  have hb : 20 * (ys.length + 1 + 1) * (L + 1) ^ 2 ≤ 40 * (L + 1) ^ 3 := by
    calc
      20 * (ys.length + 1 + 1) * (L + 1) ^ 2 ≤
          (40 * (L + 1)) * (L + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 40 * (L + 1) ^ 3 := by ring
  have hs : L + 1 ≤ (L + 1) ^ 3 := by nlinarith
  change ys.length + 1 + gcdRoundsWork (ys.length + 1) xs ys ≤ 41 * (L + 1) ^ 3
  omega

end KS.W30.BinaryGCD

end

end OAI

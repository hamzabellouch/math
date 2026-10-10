import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

section

namespace KS.W30.BinaryGCD
open KS.W19

lemma remainder_value (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    bitsValue (divideBits ys xs).2 = bitsValue xs % bitsValue ys := by
  obtain ⟨he, hr⟩ := divideBits_correct ys xs hy
  conv_rhs => rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

lemma trim_eq_nil_iff (xs : List Bool) : trimBits xs = [] ↔ bitsValue xs = 0 := by
  constructor
  · intro h
    have hv := trimBits_value xs
    rw [h] at hv
    simpa [bitsValue] using hv.symm
  · intro h
    apply canonicalBits_injective (trimBits_canonical xs) (by simp [CanonicalBits])
    simpa [bitsValue, trimBits_value] using h

lemma remainder_below_half {b r K : ℕ} (hr : 0 < r) (hrb : r < b) (hb : b < 2 * K) :
    b % r < K := by
  by_cases hsmall : r ≤ K
  · exact lt_of_lt_of_le (Nat.mod_lt b hr) hsmall
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hrb), Nat.mod_eq_of_lt (by omega)]
    omega

def gcdRounds : ℕ → List Bool → List Bool → List Bool
  | 0, xs, _ys => trimBits xs
  | k + 1, xs, ys =>
      let v := trimBits ys
      if v = [] then trimBits xs else
      let r := trimBits (divideBits v xs).2
      if r = [] then v else
      let s := trimBits (divideBits r v).2
      gcdRounds k r s

lemma gcd_two_reductions (a b : ℕ) : Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) := by
  calc
    Nat.gcd a b = Nat.gcd (a % b) b := by rw [Nat.gcd_comm a b, Nat.gcd_rec b a]
    _ = Nat.gcd (a % b) (b % (a % b)) := by
      rw [Nat.gcd_rec (a % b) b, Nat.gcd_comm]

theorem gcdRounds_correct (k : ℕ) (xs ys : List Bool) (hy : bitsValue ys < 2 ^ k) :
    bitsValue (gcdRounds (k + 1) xs ys) = Nat.gcd (bitsValue xs) (bitsValue ys) := by
  induction k generalizing xs ys with
  | zero =>
      have hz : bitsValue ys = 0 := by simpa using hy
      simp [gcdRounds, (trim_eq_nil_iff ys).mpr hz, trimBits_value, hz]
  | succ k ih =>
      let v := trimBits ys
      have hv : bitsValue v = bitsValue ys := trimBits_value ys
      by_cases hz : v = []
      · have hy0 : bitsValue ys = 0 := (trim_eq_nil_iff ys).mp hz
        simp [gcdRounds, v, hz, trimBits_value, hy0]
      · have hp : 0 < bitsValue v := canonicalBits_value_pos v (trimBits_canonical ys) hz
        let r := trimBits (divideBits v xs).2
        have hr : bitsValue r = bitsValue xs % bitsValue ys := by
          dsimp only [r]
          rw [trimBits_value, remainder_value v xs hp, hv]
        have hrb : bitsValue r < bitsValue ys := by
          rw [hr]
          exact Nat.mod_lt _ (by omega)
        by_cases hrz : r = []
        · have hm : bitsValue xs % bitsValue ys = 0 := by simpa [hrz, bitsValue] using hr.symm
          have hg : Nat.gcd (bitsValue xs) (bitsValue ys) = bitsValue ys := by
            rw [Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_zero_left]
          simp [gcdRounds, v, hz, r, hrz, hv, hg]
        · have hrp : 0 < bitsValue r := canonicalBits_value_pos r (trimBits_canonical _) hrz
          let s := trimBits (divideBits r v).2
          have hs : bitsValue s = bitsValue ys % (bitsValue xs % bitsValue ys) := by
            dsimp only [s]
            rw [trimBits_value, remainder_value r v hrp, hv, hr]
          have hslt : bitsValue s < 2 ^ k := by
            dsimp only [s]
            rw [trimBits_value, remainder_value r v hrp, hv]
            exact remainder_below_half hrp hrb (by simpa [pow_succ, Nat.mul_comm] using hy)
          have hh := ih r s hslt
          rw [hr, hs] at hh
          rw [gcdRounds]
          change bitsValue (if v = [] then trimBits xs else
            if r = [] then v else gcdRounds (k + 1) r s) = _
          simp only [hz, hrz, ite_false]
          exact hh.trans (gcd_two_reductions _ _).symm

def gcdBits (xs ys : List Bool) : List Bool := gcdRounds (ys.length + 1) xs ys

theorem gcdBits_correct (xs ys : List Bool) :
    bitsValue (gcdBits xs ys) = Nat.gcd (bitsValue xs) (bitsValue ys) :=
  gcdRounds_correct ys.length xs ys (bitsValue_lt_two_pow_length ys)

theorem gcdRounds_canonical (fuel : ℕ) (xs ys : List Bool) :
    CanonicalBits (gcdRounds fuel xs ys) := by
  induction fuel generalizing xs ys with
  | zero => exact trimBits_canonical xs
  | succ fuel ih =>
      simp only [gcdRounds]
      split
      · exact trimBits_canonical xs
      · split
        · exact trimBits_canonical ys
        · exact ih _ _

theorem gcdBits_eq_encodeNat (xs ys : List Bool) :
    gcdBits xs ys = Computability.encodeNat (Nat.gcd (bitsValue xs) (bitsValue ys)) := by
  apply canonicalBits_injective (gcdRounds_canonical _ _ _) (canonicalBits_encodeNat _)
  simpa only [gcdBits, bitsValue_encodeNat] using gcdBits_correct xs ys

theorem gcdBits_length_le_right (xs ys : List Bool) (hy : 0 < bitsValue ys) :
    (gcdBits xs ys).length ≤ ys.length := by
  rw [gcdBits_eq_encodeNat, encodeNat_length_eq_size]
  exact (Nat.size_le_size (Nat.gcd_le_right _ hy)).trans
    (Nat.size_le.mpr (bitsValue_lt_two_pow_length ys))

end KS.W30.BinaryGCD

end

end OAI

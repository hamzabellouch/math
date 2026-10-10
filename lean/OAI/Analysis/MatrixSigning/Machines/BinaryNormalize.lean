import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryDivision

namespace OAI

section

namespace KS.W19

def CanonicalBits : List Bool → Prop
  | [] => True
  | b :: bs => CanonicalBits bs ∧ (bs = [] → b = true)

def trimBits : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let tail := trimBits bs
    if tail = [] ∧ b = false then [] else b :: tail

theorem trimBits_value (xs : List Bool) : bitsValue (trimBits xs) = bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : trimBits bs = [] ∧ b = false
    · have hz : bitsValue bs = 0 := by simpa [h.1, bitsValue] using ih.symm
      simp [trimBits, h, bitsValue, hz]
    · simp [trimBits, h, bitsValue, ih]

theorem trimBits_length_le (xs : List Bool) : (trimBits xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [trimBits]
    split <;> simp_all

theorem trimBits_canonical (xs : List Bool) : CanonicalBits (trimBits xs) := by
  induction xs with
  | nil => trivial
  | cons b bs ih =>
    by_cases h : trimBits bs = [] ∧ b = false
    · simp [trimBits, h, CanonicalBits]
    · simp only [trimBits, h, ↓reduceIte, CanonicalBits]
      refine ⟨ih, ?_⟩
      intro ht
      cases b
      · exact (h ⟨ht, rfl⟩).elim
      · rfl

theorem canonicalBits_value_pos (xs : List Bool) (hc : CanonicalBits xs) (hn : xs ≠ []) :
    0 < bitsValue xs := by
  induction xs with
  | nil => exact (hn rfl).elim
  | cons b bs ih =>
    rcases hc with ⟨ht, hb⟩
    cases bs with
    | nil => simp [hb rfl, bitsValue]
    | cons c cs =>
      have h := ih ht (by simp)
      simp only [bitsValue] at h ⊢
      omega

theorem canonicalBits_injective {xs ys : List Bool}
    (hx : CanonicalBits xs) (hy : CanonicalBits ys)
    (hv : bitsValue xs = bitsValue ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    by_cases hy0 : ys = []
    · exact hy0.symm
    · have hpos := canonicalBits_value_pos ys hy hy0
      simp only [bitsValue] at hv
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have hpos := canonicalBits_value_pos (a :: as) hx (by simp)
      simp only [bitsValue] at hv hpos
      omega
    | cons b bs =>
      have hab : a = b := by
        cases a <;> cases b <;> simp_all [bitsValue, digit] <;> omega
      have htail : bitsValue as = bitsValue bs := by
        simp only [bitsValue, hab] at hv
        omega
      have heq := ih hx.1 hy.1 htail
      rw [hab, heq]

theorem canonicalBits_encodePosNum (n : PosNum) : CanonicalBits (Computability.encodePosNum n) := by
  induction n <;>
    simp_all [Computability.encodePosNum, CanonicalBits, Computability.encodePosNum_nonempty]

theorem canonicalBits_encodeNum (n : Num) : CanonicalBits (Computability.encodeNum n) := by
  cases n with
  | zero => trivial
  | pos p => exact canonicalBits_encodePosNum p

theorem canonicalBits_encodeNat (n : ℕ) : CanonicalBits (Computability.encodeNat n) :=
  canonicalBits_encodeNum n

theorem trimBits_eq_encodeNat (xs : List Bool) :
    trimBits xs = Computability.encodeNat (bitsValue xs) := by
  apply canonicalBits_injective (trimBits_canonical xs) (canonicalBits_encodeNat _)
  rw [trimBits_value, bitsValue_encodeNat]

theorem decodeNat_trimBits (xs : List Bool) :
    Computability.decodeNat (trimBits xs) = bitsValue xs := by
  rw [trimBits_eq_encodeNat, Computability.decode_encodeNat]

theorem trim_quotient_encodeNat (divisor xs : List Bool) :
    trimBits (divideBits divisor xs).1 = Computability.encodeNat (bitsValue (divideBits divisor xs).1) :=
  trimBits_eq_encodeNat _

def trimBitCost : List Bool → ℕ
  | [] => 1
  | _ :: xs => trimBitCost xs + 1

theorem trimBitCost_eq (xs : List Bool) : trimBitCost xs = xs.length + 1 := by
  induction xs <;> simp_all [trimBitCost]

theorem bitsValue_lt_two_pow_length (xs : List Bool) : bitsValue xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    have hb := digit_le_one b
    simp only [bitsValue, List.length_cons, pow_succ]
    omega

theorem trimBits_length_eq_size (xs : List Bool) :
    (trimBits xs).length = Nat.size (bitsValue xs) := by
  rw [trimBits_eq_encodeNat, encodeNat_length_eq_size]

theorem trimBits_length_le_of_value_lt (xs : List Bool) (k : ℕ)
    (hx : bitsValue xs < 2 ^ k) : (trimBits xs).length ≤ k := by
  rw [trimBits_length_eq_size]
  exact Nat.size_le.mpr hx

theorem trimBits_append_false (xs : List Bool) : trimBits (xs ++ [false]) = trimBits xs := by
  induction xs with
  | nil => simp [trimBits]
  | cons b bs ih => simp only [List.cons_append, trimBits, ih]

theorem trimBits_append_true (xs : List Bool) : trimBits (xs ++ [true]) = xs ++ [true] := by
  induction xs with
  | nil => simp [trimBits]
  | cons b bs ih => simp [trimBits, ih]

end KS.W19

end

end OAI

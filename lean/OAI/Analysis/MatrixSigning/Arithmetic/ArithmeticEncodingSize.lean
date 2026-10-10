import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticBounds
import OAI.Analysis.MatrixSigning.Arithmetic.RationalArithmetic

namespace OAI

section

namespace KS.W01

def ratLength (q : ℚ) : ℕ := (encodeRat q).length

theorem intPayload_le_natAbs (n : ℤ) : intPayload n ≤ n.natAbs := by
  cases n <;> simp [intPayload]

theorem natAbs_le_intPayload_add_one (n : ℤ) : n.natAbs ≤ intPayload n + 1 := by
  cases n <;> simp [intPayload]

theorem natAbs_size_le_payload_size_add_one (n : ℤ) :
    Nat.size n.natAbs ≤ Nat.size (intPayload n) + 1 := by
  apply Nat.size_le.mpr
  have hn := natAbs_le_intPayload_add_one n
  have hp := Nat.lt_size_self (intPayload n)
  have hpos : 0 < 2 ^ Nat.size (intPayload n) := pow_pos (by decide) _
  rw [pow_succ]
  omega

theorem rational_parts_size_le_length (q : ℚ) :
    Nat.size q.num.natAbs ≤ ratLength q ∧ Nat.size q.den ≤ ratLength q := by
  have hn := natAbs_size_le_payload_size_add_one q.num
  unfold ratLength
  rw [length_encodeRat]
  simp only [natPayloadLength_eq_size]
  constructor <;> omega

theorem rational_parts_le_two_pow_length (q : ℚ) :
    q.num.natAbs ≤ 2 ^ ratLength q ∧ q.den ≤ 2 ^ ratLength q := by
  have hs := rational_parts_size_le_length q
  constructor
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs.1)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs.2)

theorem ratLength_le_of_parts (q : ℚ) (b c : ℕ)
    (hn : q.num.natAbs ≤ 2 ^ b) (hd : q.den ≤ 2 ^ c) :
    ratLength q ≤ 2 * (b + c) + 7 := by
  have hnum := Nat.size_le_size ((intPayload_le_natAbs q.num).trans hn)
  have hden := Nat.size_le_size hd
  simp only [Nat.size_pow] at hnum hden
  unfold ratLength
  rw [length_encodeRat]
  simp only [natPayloadLength_eq_size]
  omega

theorem ratLength_mul_le (q r : ℚ) :
    ratLength (q * r) ≤ 4 * (ratLength q + ratLength r) + 7 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  have h := ratLength_le_of_parts (q * r) _ _ hn hd
  omega

theorem ratLength_add_le (q r : ℚ) :
    ratLength (q + r) ≤ 4 * (ratLength q + ratLength r) + 9 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  have h := ratLength_le_of_parts (q + r) _ _ hn hd
  omega

theorem ratLength_neg_le (q : ℚ) : ratLength (-q) ≤ 4 * ratLength q + 7 := by
  obtain ⟨hn, hd⟩ := rational_parts_le_two_pow_length q
  have h := ratLength_le_of_parts (-q) (ratLength q) (ratLength q)
    (by simpa using hn) (by simpa using hd)
  omega

theorem ratLength_sub_le (q r : ℚ) :
    ratLength (q - r) ≤ 4 * (ratLength q + ratLength r) + 9 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q (-r) (ratLength q) (ratLength r)
    hqnum hqden (by simpa using hrnum) (by simpa using hrden)
  rw [sub_eq_add_neg]
  have h := ratLength_le_of_parts (q + -r) _ _ hn hd
  omega

theorem mul_parts_size_le (q r : ℚ) :
    Nat.size (q * r).num.natAbs ≤ ratLength q + ratLength r + 1 ∧
      Nat.size (q * r).den ≤ ratLength q + ratLength r + 1 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  constructor
  · simpa only [Nat.size_pow] using Nat.size_le_size hn
  · simpa only [Nat.size_pow] using Nat.size_le_size hd

theorem add_parts_size_le (q r : ℚ) :
    Nat.size (q + r).num.natAbs ≤ ratLength q + ratLength r + 2 ∧
      Nat.size (q + r).den ≤ ratLength q + ratLength r + 1 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  constructor
  · simpa only [Nat.size_pow, Nat.add_assoc] using Nat.size_le_size hn
  · simpa only [Nat.size_pow] using Nat.size_le_size hd

def complexLength (z : RationalComplex) : ℕ := (encodeComplex z).length

@[simp] theorem complexLength_eq (z : RationalComplex) :
    complexLength z = ratLength z.1 + ratLength z.2 := by
  simp [complexLength, ratLength]

theorem complexLength_add_le (z w : RationalComplex) :
    complexLength (RationalComplex.add z w) ≤
      4 * (complexLength z + complexLength w) + 18 := by
  have hre := ratLength_add_le z.1 w.1
  have him := ratLength_add_le z.2 w.2
  simp only [complexLength_eq, RationalComplex.add]
  omega

theorem complexLength_mul_le (z w : RationalComplex) :
    complexLength (RationalComplex.mul z w) ≤
      32 * (complexLength z + complexLength w) + 130 := by
  have hrr := ratLength_mul_le z.1 w.1
  have hii := ratLength_mul_le z.2 w.2
  have hri := ratLength_mul_le z.1 w.2
  have hir := ratLength_mul_le z.2 w.1
  have hre := ratLength_sub_le (z.1 * w.1) (z.2 * w.2)
  have him := ratLength_add_le (z.1 * w.2) (z.2 * w.1)
  simp only [complexLength_eq, RationalComplex.mul]
  omega

end KS.W01

end

end OAI

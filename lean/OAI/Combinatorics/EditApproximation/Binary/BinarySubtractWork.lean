import OAI.Combinatorics.EditApproximation.Binary.BinaryOrderWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Ripple-borrow subtraction, used after the magnitude comparison in
signed-integer addition. No unit-cost operation on unbounded integers is
used by this Boolean routine. -/

namespace EditApproximation





theorem bitSubtractor_value (a b borrow : Bool) :
    a.toNat + 2 * (bitBorrow a b borrow).toNat =
      b.toNat + borrow.toNat + (bitDifference a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- Ripple-borrow subtraction when the minuend has no remaining bits. -/




theorem bitSubtractWithWork_length (left right : List Bool) (borrow : Bool) :
    (bitSubtractWithWork left right borrow).1.length = max left.length right.length := by
  induction left generalizing right borrow with
  | nil =>
    simp only [bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [bitSubtractNilLeftWithWork]
    | cons b bs ih => simp [bitSubtractNilLeftWithWork, ih]
  | cons a as ih =>
    cases right with
    | nil => simp [bitSubtractWithWork, ih]
    | cons b bs => simp [bitSubtractWithWork, ih, Nat.succ_max_succ]

private theorem bitSubtractionRippleEquation (a b borrow nextBorrow difference left right result tail : ℕ)
    (htail : result + right + nextBorrow = left + tail)
    (hbit : a + 2 * nextBorrow = b + borrow + difference) :
    (difference + 2 * result) + (b + 2 * right) + borrow =
      (a + 2 * left) + 2 * tail := by
  omega

theorem bitSubtractWithWork_value (left right : List Bool) (borrow : Bool) :
    bitWordValue (bitSubtractWithWork left right borrow).1 + bitWordValue right + borrow.toNat =
      bitWordValue left + 2 ^ max left.length right.length *
        (bitSubtractWithWork left right borrow).2.1.toNat := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => simp [bitSubtractWithWork, bitSubtractNilLeftWithWork, bitWordValue]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      have hb := bitSubtractor_value false b borrow
      simp only [bitSubtractWithWork, bitSubtractNilLeftWithWork, bitWordValue,
        List.length_nil, List.length_cons, Nat.zero_max, pow_succ, Bool.toNat_false] at h hb ⊢
      have hs := bitSubtractionRippleEquation 0 b.toNat borrow.toNat (bitBorrow false b borrow).toNat
        (bitDifference false b borrow).toNat 0 (bitWordValue bs)
        (bitWordValue (bitSubtractNilLeftWithWork bs (bitBorrow false b borrow)).1)
        (2 ^ bs.length * (bitSubtractNilLeftWithWork bs (bitBorrow false b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      have hb := bitSubtractor_value a false borrow
      simp only [bitSubtractWithWork, bitWordValue, List.length_nil, List.length_cons,
        Nat.max_zero, pow_succ, Bool.toNat_false] at h hb ⊢
      have hs := bitSubtractionRippleEquation a.toNat 0 borrow.toNat (bitBorrow a false borrow).toNat
        (bitDifference a false borrow).toNat (bitWordValue as) 0
        (bitWordValue (bitSubtractWithWork as [] (bitBorrow a false borrow)).1)
        (2 ^ as.length * (bitSubtractWithWork as [] (bitBorrow a false borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_assoc,
        Nat.mul_left_comm] using hs
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      have hb := bitSubtractor_value a b borrow
      simp only [bitSubtractWithWork, bitWordValue, List.length_cons, Nat.succ_max_succ,
        pow_succ] at h hb ⊢
      have hs := bitSubtractionRippleEquation a.toNat b.toNat borrow.toNat (bitBorrow a b borrow).toNat
        (bitDifference a b borrow).toNat (bitWordValue as) (bitWordValue bs)
        (bitWordValue (bitSubtractWithWork as bs (bitBorrow a b borrow)).1)
        (2 ^ max as.length bs.length * (bitSubtractWithWork as bs (bitBorrow a b borrow)).2.1.toNat)
        h hb
      simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hs

theorem bitWordValue_lt_pow_length (bits : List Bool) : bitWordValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitWordValue]
  | cons bit bits ih =>
    cases bit <;> simp only [bitWordValue, List.length_cons, pow_succ, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem bitSubtractWithWork_sub (left right : List Bool) (h : bitWordValue right ≤ bitWordValue left) :
    bitWordValue (bitSubtractWithWork left right false).1 = bitWordValue left - bitWordValue right := by
  have hvalue := bitSubtractWithWork_value left right false
  have hlt := bitWordValue_lt_pow_length (bitSubtractWithWork left right false).1
  rw [bitSubtractWithWork_length] at hlt
  cases hb : (bitSubtractWithWork left right false).2.1
  · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hvalue
    omega
  · simp only [hb, Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hvalue
    omega

theorem bitSubtractWithWork_cost (left right : List Bool) (borrow : Bool) :
    (bitSubtractWithWork left right borrow).2.2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => simp [bitSubtractWithWork, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractWithWork, bitSubtractNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractWithWork, List.length_cons] at *
      omega



theorem binaryNaturalSubtractWithWork_value (a b : ℕ) (h : b ≤ a) :
    bitWordValue (binaryNaturalSubtractWithWork a b).1 = a - b := by
  simpa only [binaryNaturalSubtractWithWork, bitWordValue_bits] using
    bitSubtractWithWork_sub a.bits b.bits (by simpa only [bitWordValue_bits] using h)

theorem binaryNaturalSubtractWithWork_cost (a b : ℕ) :
    (binaryNaturalSubtractWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalSubtractWithWork, Nat.size_eq_bits_len] using
    bitSubtractWithWork_cost a.bits b.bits false

end EditApproximation

end OAI

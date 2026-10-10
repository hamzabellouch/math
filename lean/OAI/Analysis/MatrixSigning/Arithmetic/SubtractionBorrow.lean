import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

section

namespace KS.W19

def subtractionBorrow : List Bool → List Bool → Bool → Bool
  | [], [], c => c
  | [], b :: bs, c => subtractionBorrow [] bs (nextBorrow false b c)
  | a :: as, [], c => subtractionBorrow as [] (nextBorrow a false c)
  | a :: as, b :: bs, c => subtractionBorrow as bs (nextBorrow a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

private theorem borrow_column_lift (a b c : Bool) (x y r carry p : Nat)
    (hr : x + carry * p = y + digit (nextBorrow a b c) + r) :
    digit a + 2 * x + carry * (p * 2) =
      digit b + 2 * y + digit c + (digit (differenceDigit a b c) + 2 * r) := by
  have hc := subtraction_column a b c
  nlinarith

theorem subtractionBorrow_identity (xs ys : List Bool) (c : Bool) :
    bitsValue xs + digit (subtractionBorrow xs ys c) * 2 ^ max xs.length ys.length =
      bitsValue ys + digit c + bitsValue (subtractBits xs ys c) := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractionBorrow, subtractBits, bitsValue]
    | cons b bs ih =>
      have ht := ih (nextBorrow false b c)
      have hh := borrow_column_lift false b c 0 (bitsValue bs)
        (bitsValue (subtractBits [] bs (nextBorrow false b c)))
        (digit (subtractionBorrow [] bs (nextBorrow false b c))) (2 ^ bs.length)
        (by simpa only [bitsValue, List.length_nil, Nat.zero_max, Nat.zero_add] using ht)
      simpa [subtractionBorrow, subtractBits, bitsValue, digit_false, pow_succ] using hh
  | cons a as ih =>
    cases ys with
    | nil =>
      have ht := ih [] (nextBorrow a false c)
      have hh := borrow_column_lift a false c (bitsValue as) 0
        (bitsValue (subtractBits as [] (nextBorrow a false c)))
        (digit (subtractionBorrow as [] (nextBorrow a false c))) (2 ^ as.length)
        (by simpa only [bitsValue, List.length_nil, Nat.max_zero, Nat.zero_add] using ht)
      simpa [subtractionBorrow, subtractBits, bitsValue, digit_false, pow_succ] using hh
    | cons b bs =>
      have ht := ih bs (nextBorrow a b c)
      have hh := borrow_column_lift a b c (bitsValue as) (bitsValue bs)
        (bitsValue (subtractBits as bs (nextBorrow a b c)))
        (digit (subtractionBorrow as bs (nextBorrow a b c))) (2 ^ max as.length bs.length) ht
      have hm : max (a :: as).length (b :: bs).length = max as.length bs.length + 1 := by
        simp only [List.length_cons]
        omega
      simpa only [subtractionBorrow, subtractBits, bitsValue, hm, pow_succ] using hh

theorem subtractionBorrow_true_iff (xs ys : List Bool) (c : Bool) :
    subtractionBorrow xs ys c = true ↔ bitsValue xs < bitsValue ys + digit c := by
  have hid := subtractionBorrow_identity xs ys c
  have hr := bitsValue_lt_two_pow_length (subtractBits xs ys c)
  rw [subtractBits_length] at hr
  cases hb : subtractionBorrow xs ys c <;> simp [hb, digit] at hid ⊢ <;> omega

def saturatingSubtractBits (xs ys : List Bool) : List Bool :=
  if subtractionBorrow xs ys false then [] else subtractBits xs ys false

theorem saturatingSubtractBits_correct (xs ys : List Bool) :
    bitsValue (saturatingSubtractBits xs ys) = bitsValue xs - bitsValue ys := by
  unfold saturatingSubtractBits
  cases hb : subtractionBorrow xs ys false
  · have hnon : bitsValue ys ≤ bitsValue xs := by
      have hh := subtractionBorrow_true_iff xs ys false
      simp only [hb, Bool.false_eq_true, digit_false, Nat.add_zero, false_iff] at hh
      omega
    have hc := subtractBits_correct xs ys false (by simpa only [digit_false, Nat.add_zero] using hnon)
    simp only [Bool.false_eq_true, ↓reduceIte, digit_false, Nat.add_zero] at hc ⊢
    omega
  · have hneg := (subtractionBorrow_true_iff xs ys false).1 hb
    simp only [digit_false, Nat.add_zero] at hneg
    simp only [↓reduceIte, bitsValue]
    omega

theorem saturatingSubtractBits_length (xs ys : List Bool) :
    (saturatingSubtractBits xs ys).length ≤ max xs.length ys.length := by
  unfold saturatingSubtractBits
  split
  · simp
  · rw [subtractBits_length]

end KS.W19

end

end OAI

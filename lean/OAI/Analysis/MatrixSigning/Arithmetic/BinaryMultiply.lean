import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdder
import OAI.Analysis.MatrixSigning.Machines.BinaryNormalize

namespace OAI

section

namespace KS.W03.BinaryMultiply

open KS.W19
open KS.W01.BinaryAdder

def shift (xs : List Bool) : List Bool := false :: xs

@[simp] theorem shift_value (xs : List Bool) : bitsValue (shift xs) = 2 * bitsValue xs := by
  simp [shift, bitsValue, digit]

@[simp] theorem shift_length (xs : List Bool) : (shift xs).length = xs.length + 1 := rfl

def multiplyRaw : List Bool → List Bool → List Bool
  | [], _ys => []
  | b :: xs, ys =>
      addBits false (if b then ys else []) (shift (multiplyRaw xs ys))

theorem multiplyRaw_correct (xs ys : List Bool) :
    bitsValue (multiplyRaw xs ys) = bitsValue xs * bitsValue ys := by
  induction xs with
  | nil => simp [multiplyRaw, bitsValue]
  | cons b xs ih =>
    cases b <;> simp [multiplyRaw, addBits_correct, bitsValue, digit, ih] <;> ring

theorem multiplyRaw_length_le (xs ys : List Bool) :
    (multiplyRaw xs ys).length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [multiplyRaw]
  | cons b xs ih =>
    have ha := addBits_length_le false (if b then ys else []) (shift (multiplyRaw xs ys))
    have hb : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    rw [multiplyRaw]
    simp only [shift_length, List.length_cons] at ha ⊢
    omega

def multiply (xs ys : List Bool) : List Bool := trimBits (multiplyRaw xs ys)

theorem multiply_correct (xs ys : List Bool) :
    bitsValue (multiply xs ys) = bitsValue xs * bitsValue ys := by
  rw [multiply, trimBits_value, multiplyRaw_correct]

theorem multiply_length_le (xs ys : List Bool) :
    (multiply xs ys).length ≤ xs.length + ys.length := by
  apply trimBits_length_le_of_value_lt
  rw [multiplyRaw_correct, pow_add]
  have hx := bitsValue_lt_two_pow_length xs
  have hy := bitsValue_lt_two_pow_length ys
  have hp : 0 < 2 ^ ys.length := pow_pos (by decide) _
  exact lt_of_le_of_lt (Nat.mul_le_mul_left (bitsValue xs) hy.le)
    (Nat.mul_lt_mul_of_pos_right hx hp)

theorem multiply_encodeNat (a b : ℕ) :
    multiply (Computability.encodeNat a) (Computability.encodeNat b) =
      Computability.encodeNat (a * b) := by
  simp [multiply, trimBits_eq_encodeNat, multiplyRaw_correct, bitsValue_encodeNat]

def rippleVisits : List Bool → List Bool → ℕ
  | [], [] => 1
  | _a :: xs, ys => rippleVisits xs ys.tail + 1
  | [], _b :: ys => rippleVisits [] ys + 1
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem rippleVisits_eq (xs ys : List Bool) :
    rippleVisits xs ys = max xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [rippleVisits]
    | cons b ys ih =>
      rw [rippleVisits, ih]
      simp
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [rippleVisits, ih]
      simp
    | cons b ys =>
      rw [rippleVisits, ih]
      simp

theorem rippleVisits_machine_correct (xs ys coins : List Bool)
    (hlen : coins.length = rippleVisits xs ys) :
    let result := machine.run (cfg (some 0) xs ys []) coins
    result.state = none ∧ result.«stacks» 0 = [] ∧ result.«stacks» 1 = [] ∧
      bitsValue ((result.«stacks» 2).reverse) = bitsValue xs + bitsValue ys := by
  apply run_correct
  simpa only [rippleVisits_eq] using hlen

def multiplyRawVisits : List Bool → List Bool → ℕ
  | [], _ys => 1
  | b :: xs, ys => multiplyRawVisits xs ys +
      rippleVisits (if b then ys else []) (shift (multiplyRaw xs ys)) + 1

theorem multiplyRawVisits_le (xs ys : List Bool) :
    multiplyRawVisits xs ys ≤ xs.length * (xs.length + ys.length + 2) + 1 := by
  induction xs with
  | nil => simp [multiplyRawVisits]
  | cons b xs ih =>
    have hlen := multiplyRaw_length_le xs ys
    have hb : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    have hcol : rippleVisits (if b then ys else []) (shift (multiplyRaw xs ys)) ≤
        2 * xs.length + ys.length + 2 := by
      rw [rippleVisits_eq, shift_length]
      omega
    rw [multiplyRawVisits]
    simp only [List.length_cons]
    nlinarith

def multiplyVisits (xs ys : List Bool) : ℕ :=
  multiplyRawVisits xs ys + trimBitCost (multiplyRaw xs ys)

theorem multiplyVisits_le (xs ys : List Bool) :
    multiplyVisits xs ys ≤ (xs.length + ys.length + 2) ^ 2 := by
  have hr := multiplyRawVisits_le xs ys
  have hl := multiplyRaw_length_le xs ys
  unfold multiplyVisits
  rw [trimBitCost_eq]
  nlinarith [Nat.zero_le (xs.length * ys.length), Nat.zero_le (ys.length * ys.length)]

def primitiveCharge (xs ys : List Bool) : ℕ := 12 * multiplyVisits xs ys

theorem primitiveCharge_le (xs ys : List Bool) :
    primitiveCharge xs ys ≤ 12 * (xs.length + ys.length + 2) ^ 2 :=
  Nat.mul_le_mul_left 12 (multiplyVisits_le xs ys)

end KS.W03.BinaryMultiply

end

end OAI

import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryMultiply

namespace OAI

section

namespace KS.W03.BinaryAccumulator

open KS.W19 KS.W01.BinaryAdder KS.W03.BinaryMultiply

def nextAccumulator (b : Bool) (operand acc : List Bool) : List Bool :=
  if b then addBits false acc operand else acc

def loop : List Bool → List Bool → List Bool → List Bool
  | [], _operand, acc => acc
  | b :: xs, operand, acc => loop xs (shift operand) (nextAccumulator b operand acc)

theorem loop_value (xs operand acc : List Bool) :
    bitsValue (loop xs operand acc) = bitsValue acc + bitsValue xs * bitsValue operand := by
  induction xs generalizing operand acc with
  | nil => simp [loop, bitsValue]
  | cons b xs ih =>
    rw [loop, ih]
    cases b <;> simp [nextAccumulator, addBits_correct, bitsValue, digit] <;> ring

def width (operand acc : List Bool) : ℕ := max operand.length acc.length

theorem next_width_le (b : Bool) (operand acc : List Bool) :
    width (shift operand) (nextAccumulator b operand acc) ≤ width operand acc + 1 := by
  have ha := addBits_length_le false acc operand
  cases b <;> simp [width, shift_length, nextAccumulator] <;> omega

theorem loop_length_le (xs operand acc : List Bool) :
    (loop xs operand acc).length ≤ width operand acc + xs.length := by
  induction xs generalizing operand acc with
  | nil => simp [loop, width]
  | cons b xs ih =>
    have hn := next_width_le b operand acc
    have hh := ih (shift operand) (nextAccumulator b operand acc)
    rw [loop]
    simp only [List.length_cons]
    omega

def bodyTicks (operand acc : List Bool) : ℕ :=
  (2 * operand.length + 2) + (max acc.length operand.length + 1) +
    ((addBits false acc operand).length + 1) + 1

theorem bodyTicks_le (operand acc : List Bool) :
    bodyTicks operand acc ≤ 4 * width operand acc + 6 := by
  have h := addBits_length_le false acc operand
  unfold bodyTicks width
  omega

def roundTicks (b : Bool) (operand acc : List Bool) : ℕ :=
  if b then bodyTicks operand acc else 0

theorem roundTicks_le (b : Bool) (operand acc : List Bool) :
    roundTicks b operand acc ≤ 4 * width operand acc + 6 := by
  cases b
  · simp [roundTicks]
  · exact bodyTicks_le operand acc

def loopTicks : List Bool → List Bool → List Bool → ℕ
  | [], _operand, _acc => 1
  | b :: xs, operand, acc =>
      1 + roundTicks b operand acc + loopTicks xs (shift operand) (nextAccumulator b operand acc)

theorem loopTicks_le (xs operand acc : List Bool) :
    loopTicks xs operand acc ≤
      8 * (xs.length + 1) * (width operand acc + xs.length + 1) := by
  induction xs generalizing operand acc with
  | nil => simp [loopTicks]; omega
  | cons b xs ih =>
    have hn := next_width_le b operand acc
    have hr := roundTicks_le b operand acc
    have ht := ih (shift operand) (nextAccumulator b operand acc)
    have ht' : loopTicks xs (shift operand) (nextAccumulator b operand acc) ≤
        8 * (xs.length + 1) * (width operand acc + xs.length + 2) := by
      apply ht.trans
      apply Nat.mul_le_mul_left
      omega
    rw [loopTicks]
    simp only [List.length_cons]
    nlinarith

theorem loop_zero_correct (xs operand : List Bool) :
    bitsValue (loop xs operand []) = bitsValue xs * bitsValue operand := by
  simpa [bitsValue] using loop_value xs operand []

theorem loop_zero_length_le (xs operand : List Bool) :
    (loop xs operand []).length ≤ xs.length + operand.length := by
  simpa [width, Nat.add_comm] using loop_length_le xs operand []

theorem loop_zero_ticks_le (xs operand : List Bool) :
    loopTicks xs operand [] ≤ 8 * (xs.length + operand.length + 1) ^ 2 := by
  have h := loopTicks_le xs operand []
  simp only [width, List.length_nil, Nat.max_zero] at h
  have hn : xs.length + 1 ≤ xs.length + operand.length + 1 := by omega
  calc
    _ ≤ 8 * (xs.length + 1) * (operand.length + xs.length + 1) := h
    _ ≤ 8 * (xs.length + operand.length + 1) * (xs.length + operand.length + 1) := by
      rw [Nat.add_comm operand.length xs.length]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hn)
    _ = _ := by ring

theorem loop_trim_eq_multiply (xs operand : List Bool) :
    trimBits (loop xs operand []) = multiply xs operand := by
  rw [trimBits_eq_encodeNat, loop_zero_correct]
  unfold multiply
  rw [trimBits_eq_encodeNat, multiplyRaw_correct]

end KS.W03.BinaryAccumulator

end

end OAI

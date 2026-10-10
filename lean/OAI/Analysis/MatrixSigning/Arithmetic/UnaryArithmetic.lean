import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryDivision

namespace OAI

section

namespace KS.W03.UnaryArithmetic
open KS.W19

def accumulate : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => accumulate bs (2 * n + digit b)

theorem accumulate_append (xs ys : List Bool) (n : ℕ) :
    accumulate (xs ++ ys) n = accumulate ys (accumulate xs n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons b bs ih => exact ih (2 * n + digit b)

theorem accumulate_affine (xs : List Bool) (n : ℕ) :
    accumulate xs n = 2 ^ xs.length * n + accumulate xs 0 := by
  induction xs generalizing n with
  | nil => simp [accumulate]
  | cons b bs ih =>
    simp only [accumulate, List.length_cons]
    rw [ih (2 * n + digit b), ih (2 * 0 + digit b), pow_succ]
    ring

theorem accumulate_reverse (xs : List Bool) :
    accumulate xs.reverse 0 = bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, accumulate_append]
    simp only [accumulate, ih, bitsValue]
    omega

theorem le_accumulate (xs : List Bool) (n : ℕ) : n ≤ accumulate xs n := by
  induction xs generalizing n with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (by omega : n ≤ 2 * n + digit b).trans (ih _)

def ticks : List Bool → ℕ → ℕ
  | [], _ => 1
  | b :: bs, n => 4 * n + 3 + ticks bs (2 * n + digit b)

theorem ticks_le (xs : List Bool) (n : ℕ) :
    ticks xs n ≤ 4 * (accumulate xs n + 1) * (xs.length + 1) := by
  induction xs generalizing n with
  | nil => simp [ticks, accumulate]; omega
  | cons b bs ih =>
    have h := ih (2 * n + digit b)
    have hn := le_accumulate (b :: bs) n
    simp only [ticks, accumulate, List.length_cons] at *
    nlinarith

theorem ticks_le_linear (xs : List Bool) (n : ℕ) :
    ticks xs n + 4 * n ≤ 4 * accumulate xs n + 3 * xs.length + 1 := by
  induction xs generalizing n with
  | nil => simp only [ticks, accumulate, List.length_nil]; omega
  | cons b bs ih =>
    have h := ih (2 * n + digit b)
    simp only [ticks, accumulate, List.length_cons]
    omega

def totalTicks (xs : List Bool) : ℕ := xs.length + 1 + ticks xs.reverse 0

theorem totalTicks_le_linear (xs : List Bool) :
    totalTicks xs ≤ 4 * bitsValue xs + 4 * xs.length + 2 := by
  have ht := ticks_le_linear xs.reverse 0
  rw [accumulate_reverse, List.length_reverse] at ht
  unfold totalTicks
  omega

theorem totalTicks_le (xs : List Bool) :
    totalTicks xs ≤ 5 * (bitsValue xs + xs.length + 1) ^ 2 := by
  have ht := ticks_le xs.reverse 0
  rw [accumulate_reverse, List.length_reverse] at ht
  unfold totalTicks
  nlinarith [Nat.zero_le (bitsValue xs * bitsValue xs),
    Nat.zero_le (xs.length * xs.length)]

end KS.W03.UnaryArithmetic

end

end OAI

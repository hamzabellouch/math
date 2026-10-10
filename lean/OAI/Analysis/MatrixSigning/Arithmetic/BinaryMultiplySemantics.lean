import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryMultiply

namespace OAI

section

namespace KS.W03.BinaryMultiply

open KS.W19
open KS.W01.BinaryAdder

inductive RippleExec : Bool → List Bool → List Bool → List Bool → ℕ → Prop
  | done (c : Bool) : RippleExec c [] [] (if c then [true] else []) 1
  | left {c a : Bool} {xs ys result : List Bool} {steps : ℕ}
      (tail : RippleExec (carryBit a (ys.headD false) c) xs ys.tail result steps) :
      RippleExec c (a :: xs) ys (sumBit a (ys.headD false) c :: result) (steps + 1)
  | right {c b : Bool} {ys result : List Bool} {steps : ℕ}
      (tail : RippleExec (carryBit false b c) [] ys result steps) :
      RippleExec c [] (b :: ys) (sumBit false b c :: result) (steps + 1)

theorem ripple_execution (c : Bool) (xs ys : List Bool) :
    RippleExec c xs ys (addBits c xs ys) (rippleVisits xs ys) := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simpa only [addBits, rippleVisits] using RippleExec.done c
    | cons b ys ih =>
      simpa only [addBits, rippleVisits] using
        (RippleExec.right (c := c) (b := b) (ih (carryBit false b c)))
  | cons a xs ih =>
    simpa only [addBits, rippleVisits] using
      (RippleExec.left (c := c) (a := a)
        (ih (carryBit a (ys.headD false) c) ys.tail))

theorem RippleExec.unique {c : Bool} {xs ys out : List Bool} {steps : ℕ}
    (h : RippleExec c xs ys out steps) :
    out = addBits c xs ys ∧ steps = rippleVisits xs ys := by
  induction h with
  | done c => exact ⟨by rw [addBits], by rw [rippleVisits]⟩
  | @left c a xs ys result steps h ih =>
    rcases ih with ⟨rfl, rfl⟩
    exact ⟨by rw [addBits], by rw [rippleVisits]⟩
  | @right c b ys result steps h ih =>
    rcases ih with ⟨rfl, rfl⟩
    exact ⟨by rw [addBits], by rw [rippleVisits]⟩

inductive RawMultiplyExec : List Bool → List Bool → List Bool → ℕ → Prop
  | done (ys : List Bool) : RawMultiplyExec [] ys [] 1
  | step {b : Bool} {xs ys tail out : List Bool} {recursiveSteps addSteps : ℕ}
      (recursive : RawMultiplyExec xs ys tail recursiveSteps)
      (addition : RippleExec false (if b then ys else []) (shift tail) out addSteps) :
      RawMultiplyExec (b :: xs) ys out (recursiveSteps + addSteps + 1)

theorem multiplyRaw_execution (xs ys : List Bool) :
    RawMultiplyExec xs ys (multiplyRaw xs ys) (multiplyRawVisits xs ys) := by
  induction xs with
  | nil => exact RawMultiplyExec.done ys
  | cons b xs ih =>
    exact RawMultiplyExec.step ih
      (ripple_execution false (if b then ys else []) (shift (multiplyRaw xs ys)))

theorem RawMultiplyExec.unique {xs ys out : List Bool} {steps : ℕ}
    (h : RawMultiplyExec xs ys out steps) :
    out = multiplyRaw xs ys ∧ steps = multiplyRawVisits xs ys := by
  induction h with
  | done ys => exact ⟨rfl, rfl⟩
  | @step b xs ys tail out recursiveSteps addSteps hrec hadd ih =>
    obtain ⟨rfl, rfl⟩ := ih
    obtain ⟨rfl, rfl⟩ := hadd.unique
    exact ⟨rfl, rfl⟩

inductive TrimExec : List Bool → List Bool → ℕ → Prop
  | done : TrimExec [] [] 1
  | step {b : Bool} {xs tail : List Bool} {steps : ℕ}
      (recursive : TrimExec xs tail steps) :
      TrimExec (b :: xs) (if tail = [] ∧ b = false then [] else b :: tail) (steps + 1)

theorem trim_execution (xs : List Bool) :
    TrimExec xs (trimBits xs) (trimBitCost xs) := by
  induction xs with
  | nil => exact TrimExec.done
  | cons b xs ih => exact TrimExec.step ih

theorem TrimExec.unique {xs out : List Bool} {steps : ℕ}
    (h : TrimExec xs out steps) : out = trimBits xs ∧ steps = trimBitCost xs := by
  induction h with
  | done => exact ⟨rfl, rfl⟩
  | @step b xs tail steps h ih =>
    obtain ⟨rfl, rfl⟩ := ih
    exact ⟨rfl, rfl⟩

inductive MultiplyExec : List Bool → List Bool → List Bool → ℕ → Prop
  | run {xs ys raw out : List Bool} {rawSteps trimSteps : ℕ}
      (rawExecution : RawMultiplyExec xs ys raw rawSteps)
      (normalization : TrimExec raw out trimSteps) :
      MultiplyExec xs ys out (rawSteps + trimSteps)

theorem multiply_execution (xs ys : List Bool) :
    MultiplyExec xs ys (multiply xs ys) (multiplyVisits xs ys) :=
  MultiplyExec.run (multiplyRaw_execution xs ys) (trim_execution (multiplyRaw xs ys))

theorem MultiplyExec.unique {xs ys out : List Bool} {steps : ℕ}
    (h : MultiplyExec xs ys out steps) : out = multiply xs ys ∧ steps = multiplyVisits xs ys := by
  cases h with
  | run hraw htrim =>
    obtain ⟨rfl, rfl⟩ := hraw.unique
    obtain ⟨rfl, rfl⟩ := htrim.unique
    exact ⟨rfl, rfl⟩

theorem execution_correct_and_bounded {xs ys out : List Bool} {steps : ℕ}
    (h : MultiplyExec xs ys out steps) :
    bitsValue out = bitsValue xs * bitsValue ys ∧
      out.length ≤ xs.length + ys.length ∧
      steps ≤ (xs.length + ys.length + 2) ^ 2 := by
  obtain ⟨rfl, rfl⟩ := h.unique
  exact ⟨multiply_correct xs ys, multiply_length_le xs ys, multiplyVisits_le xs ys⟩

theorem exists_execution (xs ys : List Bool) :
    ∃ out steps, MultiplyExec xs ys out steps ∧
      bitsValue out = bitsValue xs * bitsValue ys ∧
      out.length ≤ xs.length + ys.length ∧
      steps ≤ (xs.length + ys.length + 2) ^ 2 :=
  ⟨multiply xs ys, multiplyVisits xs ys, multiply_execution xs ys,
    execution_correct_and_bounded (multiply_execution xs ys)⟩

end KS.W03.BinaryMultiply

end

end OAI

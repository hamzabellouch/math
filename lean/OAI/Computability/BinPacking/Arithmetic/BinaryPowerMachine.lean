import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Computability.BinPacking.Arithmetic.BinaryTallyMachine

namespace OAI

namespace BinPackingGap.BinaryMulMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryAddMachine.State A

def clean (ambient : A) : State A := (((ambient, false), none), none)

inductive Label
  | copyLeft | forkLeft | copyRight | forkRight | guard
  | copyAddend | forkAddend | add | restoreSum | shift
  | clearShift | reverseOutput | output
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyLeft, .forkLeft, .copyRight, .forkRight,
  .guard, .copyAddend, .forkAddend, .add, .restoreSum, .shift, .clearShift, .reverseOutput,
  .output]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def statement (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyLeft => MachineTransfer.loopAt (slots 0) (slots 8) id false
      (labels .copyLeft) (some (labels .forkLeft))
  | .forkLeft => MachineCopy.forkLoop (slots 8) (slots 0) (slots 3) false
      (labels .forkLeft) (some (labels .copyRight))
  | .copyRight => MachineTransfer.loopAt (slots 1) (slots 8) id false
      (labels .copyRight) (some (labels .forkRight))
  | .forkRight => MachineCopy.forkLoop (slots 8) (slots 1) (slots 4) false
      (labels .forkRight) (some (labels .guard))
  | .guard => .pop (slots 4) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.branch (fun state => state.2.getD false)
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .copyAddend))
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .shift)))
        (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .clearShift)))
  | .copyAddend => MachineTransfer.loopAt (slots 3) (slots 8) id false
      (labels .copyAddend) (some (labels .forkAddend))
  | .forkAddend => MachineCopy.forkLoop (slots 8) (slots 3) (slots 6) false
      (labels .forkAddend) (some (labels .add))
  | .add => BinaryAddMachine.addLoop (slots 6) (slots 5) (slots 7)
      (labels .add) (some (labels .restoreSum))
  | .restoreSum => MachineTransfer.loopAt (slots 7) (slots 5) id false
      (labels .restoreSum) (some (labels .shift))
  | .shift => .peek (slots 3) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.push (slots 3) (fun _ => false)
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .guard)))
        (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .guard)))
  | .clearShift => MachineDrain.drain (slots 3) (labels .clearShift)
      (some (labels .reverseOutput))
  | .reverseOutput => MachineTransfer.loopAt (slots 5) (slots 7) id false
      (labels .reverseOutput) (some (labels .output))
  | .output => MachineTransfer.loopAt (slots 7) (slots 2) id false
      (labels .output) exit

def program (slots : Fin 9 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State A) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 9
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .copyLeft
  σ := State Unit
  initialState := clean ()
  m := program (Function.Embedding.refl (Fin 9))

noncomputable def framedTapes (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) : K → List Bool := fun k =>
  if h : ∃ i, slots i = k then words (Classical.choose h) else base k

@[simp] theorem framedTapes_slot (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (i : Fin 9) :
    framedTapes slots base words (slots i) = words i := by
  unfold framedTapes
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact slots.injective (Classical.choose_spec (show ∃ j, slots j = slots i from ⟨i, rfl⟩))

theorem framedTapes_other (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (k : K) (hk : ¬ ∃ i, slots i = k) :
    framedTapes slots base words k = base k := by
  simp [framedTapes, hk]

theorem framedTapes_update (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) (i : Fin 9) (word : List Bool) :
    Function.update (framedTapes slots base words) (slots i) word =
      framedTapes slots base (Function.update words i word) := by
  funext k
  by_cases hk : ∃ j, slots j = k
  · obtain ⟨j, rfl⟩ := hk
    by_cases hji : j = i
    · subst j; simp
    · simp [Function.update_of_ne, hji, slots.injective.ne hji]
  · have hki : k ≠ slots i := fun h => hk ⟨i, h.symm⟩
    simp [Function.update_of_ne hki, framedTapes_other slots base _ k hk]

noncomputable def tapes (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch : List Bool) :
    K → List Bool :=
  framedTapes slots base ![left, right, output, shifted, remaining, accumulator,
    addend, reversed, scratch]

def loopSteps (xs : List Bool) : List Bool → List Bool → Nat
  | [], acc => xs.length + 2 * acc.length + 4
  | false :: ys, acc => loopSteps (BinaryArithmetic.shift xs) ys acc + 2
  | true :: ys, acc =>
      loopSteps (BinaryArithmetic.shift xs) ys (BinaryArithmetic.addCarry xs acc false) +
        (2 * xs.length + max xs.length acc.length +
          (BinaryArithmetic.addCarry xs acc false).length + 6)

def steps (xs ys : List Bool) : Nat :=
  loopSteps xs ys [] + (2 * (ys.length + 1) + 2 * (xs.length + 1))

@[simp] theorem tapes_slot (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch : List Bool) (i : Fin 9) :
    tapes slots base left right output shifted remaining accumulator addend reversed scratch (slots i) =
      ![left, right, output, shifted, remaining, accumulator, addend, reversed, scratch] i :=
  framedTapes_slot slots base _ i

@[simp] private theorem tapes_update0 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 0) replacement =
      tapes slots base replacement right output shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update1 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 1) replacement =
      tapes slots base left replacement output shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update2 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 2) replacement =
      tapes slots base left right replacement shifted remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update3 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 3) replacement =
      tapes slots base left right output replacement remaining accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update4 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 4) replacement =
      tapes slots base left right output shifted replacement accumulator addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update5 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 5) replacement =
      tapes slots base left right output shifted remaining replacement addend reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update6 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 6) replacement =
      tapes slots base left right output shifted remaining accumulator replacement reversed scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update7 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 7) replacement =
      tapes slots base left right output shifted remaining accumulator addend replacement scratch := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

@[simp] private theorem tapes_update8 (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right output shifted remaining accumulator addend reversed scratch replacement : List Bool) :
    Function.update (tapes slots base left right output shifted remaining accumulator addend reversed scratch)
      (slots 8) replacement =
      tapes slots base left right output shifted remaining accumulator addend reversed replacement := by
  unfold tapes
  rw [framedTapes_update]
  congr 1
  funext j
  fin_cases j <;> simp

private theorem composeTrace {S : Type} {f : S → S} {n m : Nat} {a b c : S}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[m + n] a = c := by
  rw [Function.iterate_add_apply, first, second]

section Traces

variable (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
variable (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
variable (base : K → List Bool) (left right out : List Bool) (ambient : A)

include atLabels

private theorem copyInputsTrace :
    (MachineComposition.advance (TM2.step p))^[2 * (right.length + 1) + 2 * (left.length + 1)]
      (some ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩) =
      some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out left right [] [] [] []⟩ := by
  have hleft :
      (MachineComposition.advance (TM2.step p))^[2 * (left.length + 1)]
        (some ⟨some (labels .copyLeft), clean ambient,
          tapes slots base left right out [] [] [] [] [] []⟩) =
        some ⟨some (labels .copyRight), clean ambient,
          tapes slots base left right out left [] [] [] [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 0) (slots 3) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyLeft) (labels .forkLeft)
      (some (labels .copyRight)) p (atLabels .copyLeft) (atLabels .forkLeft)
      (tapes slots base left right out [] [] [] [] [] []) (by simp)
      ((ambient, false), none) none
  have hright :
      (MachineComposition.advance (TM2.step p))^[2 * (right.length + 1)]
        (some ⟨some (labels .copyRight), clean ambient,
          tapes slots base left right out left [] [] [] [] []⟩) =
        some ⟨some (labels .guard), clean ambient,
          tapes slots base left right out left right [] [] [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 1) (slots 4) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyRight) (labels .forkRight)
      (some (labels .guard)) p (atLabels .copyRight) (atLabels .forkRight)
      (tapes slots base left right out left [] [] [] [] []) (by simp)
      ((ambient, false), none) none
  exact composeTrace hleft hright

private theorem guardEmptyTrace (xs acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩) =
      some ⟨some (labels .clearShift), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [statement, TM2.stepAux, clean]

private theorem guardConsTrace (xs ys acc : List Bool) (bit : Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs (bit :: ys) acc [] [] []⟩) =
      some ⟨some (labels (if bit then .copyAddend else .shift)), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .guard)) _ _) = _
  rw [atLabels .guard]
  cases bit <;> simp [statement, TM2.stepAux, clean]

private theorem shiftTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .shift), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out (BinaryArithmetic.shift xs) ys acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .shift)) _ _) = _
  rw [atLabels .shift]
  cases xs <;> simp [statement, TM2.stepAux, clean, BinaryArithmetic.shift]

private theorem addPhaseTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[
        ((BinaryArithmetic.addCarry xs acc false).length + 1) +
          ((max xs.length acc.length + 1) + 2 * (xs.length + 1))]
      (some ⟨some (labels .copyAddend), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨some (labels .shift), clean ambient,
        tapes slots base left right out xs ys (BinaryArithmetic.addCarry xs acc false)
          [] [] []⟩ := by
  have hcopy :
      (MachineComposition.advance (TM2.step p))^[2 * (xs.length + 1)]
        (some ⟨some (labels .copyAddend), clean ambient,
          tapes slots base left right out xs ys acc [] [] []⟩) =
        some ⟨some (labels .add), clean ambient,
          tapes slots base left right out xs ys acc xs [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 3) (slots 6) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyAddend) (labels .forkAddend)
      (some (labels .add)) p (atLabels .copyAddend) (atLabels .forkAddend)
      (tapes slots base left right out xs ys acc [] [] []) (by simp)
      ((ambient, false), none) none
  have hadd :
      (MachineComposition.advance (TM2.step p))^[max xs.length acc.length + 1]
        (some ⟨some (labels .add), clean ambient,
          tapes slots base left right out xs ys acc xs [] []⟩) =
        some ⟨some (labels .restoreSum), clean ambient,
          tapes slots base left right out xs ys [] []
            (BinaryArithmetic.addCarry xs acc false).reverse []⟩ := by
    simpa [BinaryAddMachine.tapes, BinaryAddMachine.clean, BinaryAddMachine.state, clean]
      using BinaryAddMachine.addTrace (slots 6) (slots 5) (slots 7)
        (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
        (slots.injective.ne (by decide)) (labels .add) (some (labels .restoreSum))
        p (atLabels .add) (tapes slots base left right out xs ys acc xs [] [])
        ambient xs acc [] false none none
  have hrestore :
      (MachineComposition.advance (TM2.step p))^[(BinaryArithmetic.addCarry xs acc false).length + 1]
        (some ⟨some (labels .restoreSum), clean ambient,
          tapes slots base left right out xs ys [] []
            (BinaryArithmetic.addCarry xs acc false).reverse []⟩) =
        some ⟨some (labels .shift), clean ambient,
          tapes slots base left right out xs ys (BinaryArithmetic.addCarry xs acc false)
            [] [] []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 5) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 7) (slots 5)
        (slots.injective.ne (by decide)) id false (labels .restoreSum)
        (some (labels .shift)) p (atLabels .restoreSum)
        (tapes slots base left right out xs ys [] []
          (BinaryArithmetic.addCarry xs acc false).reverse [])
        ((ambient, false), none) none
  exact composeTrace (composeTrace hcopy hadd) hrestore

private theorem cleanupTrace (xs acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[xs.length + 2 * acc.length + 3]
      (some ⟨some (labels .clearShift), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (acc ++ out) [] [] [] [] [] []⟩ := by
  have hclear :
      (MachineComposition.advance (TM2.step p))^[xs.length + 1]
        (some ⟨some (labels .clearShift), clean ambient,
          tapes slots base left right out xs [] acc [] [] []⟩) =
        some ⟨some (labels .reverseOutput), clean ambient,
          tapes slots base left right out [] [] acc [] [] []⟩ := by
    simpa [clean] using MachineDrain.drainTrace (slots 3) (labels .clearShift)
      (some (labels .reverseOutput)) p (atLabels .clearShift)
      (tapes slots base left right out xs [] acc [] [] []) xs ((ambient, false), none) none
  have hreverse :
      (MachineComposition.advance (TM2.step p))^[acc.length + 1]
        (some ⟨some (labels .reverseOutput), clean ambient,
          tapes slots base left right out [] [] acc [] [] []⟩) =
        some ⟨some (labels .output), clean ambient,
          tapes slots base left right out [] [] [] [] acc.reverse []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 7) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 5) (slots 7)
        (slots.injective.ne (by decide)) id false (labels .reverseOutput)
        (some (labels .output)) p (atLabels .reverseOutput)
        (tapes slots base left right out [] [] acc [] [] []) ((ambient, false), none) none
  have houtput :
      (MachineComposition.advance (TM2.step p))^[acc.length + 1]
        (some ⟨some (labels .output), clean ambient,
          tapes slots base left right out [] [] [] [] acc.reverse []⟩) =
        some ⟨exit, clean ambient,
          tapes slots base left right (acc ++ out) [] [] [] [] [] []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 2) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 7) (slots 2)
        (slots.injective.ne (by decide)) id false (labels .output) exit p (atLabels .output)
        (tapes slots base left right out [] [] [] [] acc.reverse [])
        ((ambient, false), none) none
  rw [show xs.length + 2 * acc.length + 3 =
    (acc.length + 1) + ((acc.length + 1) + (xs.length + 1)) by omega]
  exact composeTrace (composeTrace hclear hreverse) houtput

theorem loopTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[loopSteps xs ys acc]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc xs ys acc ++ out)
          [] [] [] [] [] []⟩ := by
  induction ys generalizing xs acc with
  | nil =>
      rw [show loopSteps xs [] acc = (xs.length + 2 * acc.length + 3) + 1 by
        simp only [loopSteps]]
      exact composeTrace
        (guardEmptyTrace slots labels exit p atLabels base left right out ambient xs acc)
        (cleanupTrace slots labels exit p atLabels base left right out ambient xs acc)
  | cons bit ys ih =>
      cases bit with
      | false =>
          rw [show loopSteps xs (false :: ys) acc =
            (loopSteps (BinaryArithmetic.shift xs) ys acc + 1) + 1 by
              simp only [loopSteps]]
          exact composeTrace
            (guardConsTrace slots labels exit p atLabels base left right out ambient xs ys acc false)
            (composeTrace
              (shiftTrace slots labels exit p atLabels base left right out ambient xs ys acc)
              (ih (BinaryArithmetic.shift xs) acc))
      | true =>
          rw [show loopSteps xs (true :: ys) acc =
            ((loopSteps (BinaryArithmetic.shift xs) ys (BinaryArithmetic.addCarry xs acc false) + 1) +
              (((BinaryArithmetic.addCarry xs acc false).length + 1) +
                ((max xs.length acc.length + 1) + 2 * (xs.length + 1)))) + 1 by
                  simp only [loopSteps]
                  omega]
          exact composeTrace
            (guardConsTrace slots labels exit p atLabels base left right out ambient xs ys acc true)
            (composeTrace
              (addPhaseTrace slots labels exit p atLabels base left right out ambient xs ys acc)
              (composeTrace
                (shiftTrace slots labels exit p atLabels base left right out ambient xs ys
                  (BinaryArithmetic.addCarry xs acc false))
                (ih (BinaryArithmetic.shift xs) (BinaryArithmetic.addCarry xs acc false))))

theorem multiplyTrace :
    (MachineComposition.advance (TM2.step p))^[steps left right]
      (some ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc left right [] ++ out)
          [] [] [] [] [] []⟩ :=
  composeTrace (copyInputsTrace slots labels exit p atLabels base left right out ambient)
    (loopTrace slots labels exit p atLabels base left right out ambient left right [])

end Traces

theorem loopSteps_le (xs ys acc : List Bool) :
    loopSteps xs ys acc ≤
      (ys.length + 1) * (4 * (max xs.length acc.length + ys.length) + 8) := by
  induction ys generalizing xs acc with
  | nil =>
      have hx := Nat.le_max_left xs.length acc.length
      have ha := Nat.le_max_right xs.length acc.length
      simp only [loopSteps, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.one_mul]
      omega
  | cons bit ys ih =>
      have hx := Nat.le_max_left xs.length acc.length
      have ha := Nat.le_max_right xs.length acc.length
      have hs := BinaryArithmetic.shift_length_le xs
      cases bit with
      | false =>
          have hp : max (BinaryArithmetic.shift xs).length acc.length + ys.length ≤
              max xs.length acc.length + (ys.length + 1) := by omega
          have h := (ih (BinaryArithmetic.shift xs) acc).trans
            (Nat.mul_le_mul_left (ys.length + 1)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hp) 8))
          simp only [loopSteps, List.length_cons]
          nlinarith
      | true =>
          have hadd := BinaryArithmetic.addCarry_length xs acc false
          have hp : max (BinaryArithmetic.shift xs).length
                (BinaryArithmetic.addCarry xs acc false).length + ys.length ≤
              max xs.length acc.length + (ys.length + 1) := by omega
          have h := (ih (BinaryArithmetic.shift xs) (BinaryArithmetic.addCarry xs acc false)).trans
            (Nat.mul_le_mul_left (ys.length + 1)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hp) 8))
          simp only [loopSteps, List.length_cons]
          nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 14 * Polynomial.X + Polynomial.C 12

theorem steps_le_timePolynomial (xs ys : List Bool) :
    steps xs ys ≤ timePolynomial.eval (xs.length + ys.length) := by
  have hloop := loopSteps_le xs ys []
  simp only [List.length_nil, Nat.max_zero] at hloop
  have hproduct := Nat.mul_le_mul_right (4 * (xs.length + ys.length) + 8)
    (show ys.length + 1 ≤ (xs.length + ys.length) + 1 by omega)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

def multiplyInTime (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (left right out : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩
      (some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc left right [] ++ out)
          [] [] [] [] [] []⟩) (steps left right) where
  steps := steps left right
  evals_in_steps := multiplyTrace slots labels exit p atLabels base left right out ambient
  steps_le_m := Nat.le_refl _

def multiplyInPolynomialTime (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (left right out : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩
      (some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc left right [] ++ out)
          [] [] [] [] [] []⟩)
      (timePolynomial.eval (left.length + right.length)) where
  steps := steps left right
  evals_in_steps := multiplyTrace slots labels exit p atLabels base left right out ambient
  steps_le_m := steps_le_timePolynomial left right

theorem multiplyNatTrace (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (out : List Bool) (ambient : A) :
    (MachineComposition.advance (TM2.step p))^[steps a.bits b.bits]
      (some ⟨some (labels .copyLeft), clean ambient,
        tapes slots base a.bits b.bits out [] [] [] [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base a.bits b.bits ((a * b).bits ++ out) [] [] [] [] [] []⟩ := by
  simpa only [BinaryArithmetic.mulAcc_bits] using
    multiplyTrace slots labels exit p atLabels base a.bits b.bits out ambient

theorem multiplyFrame (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right out result : List Bool) (k : K) (hk : k ≠ slots 2) :
    tapes slots base left right (result ++ out) [] [] [] [] [] [] k =
      tapes slots base left right out [] [] [] [] [] [] k := by
  rw [← tapes_update2 slots base left right out [] [] [] [] [] [] (result ++ out)]
  simp only [Function.update_of_ne hk]

private theorem initialTapes_eq (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right : List Bool) (hleft : base (slots 0) = left) (hright : base (slots 1) = right)
    (workspace : ∀ i : Fin 9, 3 ≤ i.val → base (slots i) = []) :
    tapes slots base left right (base (slots 2)) [] [] [] [] [] [] = base := by
  have h3 := workspace 3 (by decide)
  have h4 := workspace 4 (by decide)
  have h5 := workspace 5 (by decide)
  have h6 := workspace 6 (by decide)
  have h7 := workspace 7 (by decide)
  have h8 := workspace 8 (by decide)
  funext k
  by_cases hk : ∃ i, slots i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [tapes_slot]
    fin_cases i <;> simp_all
  · exact framedTapes_other slots base _ k hk

def multiplyNatInPolynomialTime (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat)
    (operandA : base (slots 0) = a.bits) (operandB : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 9, 3 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyLeft), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (slots 2) ((a * b).bits ++ base (slots 2))⟩)
      (timePolynomial.eval (a.size + b.size)) := by
  have hbase := initialTapes_eq slots base a.bits b.bits operandA operandB workspace
  have hfinish : tapes slots base a.bits b.bits ((a * b).bits ++ base (slots 2))
      [] [] [] [] [] [] = Function.update base (slots 2) ((a * b).bits ++ base (slots 2)) := by
    rw [← tapes_update2 slots base a.bits b.bits (base (slots 2)) [] [] [] [] [] [], hbase]
  have h := multiplyInPolynomialTime slots labels exit p atLabels base a.bits b.bits
    (base (slots 2)) ambient
  simpa only [BinaryArithmetic.mulAcc_bits, hbase, hfinish, ← Nat.size_eq_bits_len] using h

def programNatInPolynomialTime (slots : Fin 9 ↪ K) (base : K → List Bool) (a b : Nat)
    (operandA : base (slots 0) = a.bits) (operandB : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 9, 3 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program (A := A) slots))
      ⟨some .copyLeft, clean ambient, base⟩
      (some ⟨none, clean ambient,
        Function.update base (slots 2) ((a * b).bits ++ base (slots 2))⟩)
      (timePolynomial.eval (a.size + b.size)) :=
  multiplyNatInPolynomialTime slots id none (program slots) (fun _ => rfl)
    base a b operandA operandB workspace ambient

end BinPackingGap.BinaryMulMachine

namespace BinPackingGap.BinaryPowerMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | initialize | guard | multiply (phase : BinaryMulMachine.Label)
  | clearAccumulator | reverseProduct | restoreAccumulator
  deriving DecidableEq, Fintype

def mulSlots (slots : Fin 11 ↪ K) : Fin 9 ↪ K where
  toFun i := slots ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    have h' := congrArg Fin.val (slots.injective h)
    exact Fin.ext h'

def instruction (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .initialize => .push (slots 1) (fun _ => true)
      (.load (fun s => clean s.1.1.1) (.goto fun _ => labels .guard))
  | .guard => .pop (slots 9) (fun s head => (s.1, head))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => clean s.1.1.1)
          (.goto fun _ => labels (.multiply .copyLeft)))
        (BinaryAddMachine.finish exit))
  | .multiply phase => BinaryMulMachine.statement (mulSlots slots)
      (fun phase => labels (.multiply phase)) (some (labels .clearAccumulator)) phase
  | .clearAccumulator => MachineDrain.drain (slots 1) (labels .clearAccumulator)
      (some (labels .reverseProduct))
  | .reverseProduct => loopAt (slots 2) (slots 10) id false
      (labels .reverseProduct) (some (labels .restoreAccumulator))
  | .restoreAccumulator => loopAt (slots 10) (slots 1) id false
      (labels .restoreAccumulator) (some (labels .guard))

def program (slots : Fin 11 ↪ K) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Label (State A) :=
  instruction slots id none

def machine : FinTM2 where
  K := Fin 11
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .initialize
  σ := State Unit
  initialState := clean ()
  m := program (Function.Embedding.refl (Fin 11))

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine := by
  intro k
  change Finite Bool
  infer_instance

def Workspace (slots : Fin 11 ↪ K) (base : K → List Bool) : Prop :=
  ∀ i : Fin 11, 2 ≤ i.val → i.val ≠ 9 → base (slots i) = []

noncomputable def bodyBudget (a r : Nat) : Nat :=
  1 + BinaryMulMachine.timePolynomial.eval (a.size + r.size) +
    (r.size + 1) + ((a * r).size + 1) + ((a * r).size + 1)

noncomputable def loopBudget (a : Nat) : Nat → List Bool → Nat
  | _, [] => 1
  | r, _ :: tally => bodyBudget a r + loopBudget a (a * r) tally

def appendRuns {X : Type} (step : X → Option X) {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    change (MachineComposition.advance step)^[first.steps + second.steps] (some a) = some c
    rw [Nat.add_comm, Function.iterate_add_apply]
    have hfirst := first.evals_in_steps
    have hsecond := second.evals_in_steps
    change (MachineComposition.advance step)^[first.steps] (some a) = some b at hfirst
    change (MachineComposition.advance step)^[second.steps] (some b) = some c at hsecond
    rw [hfirst]
    exact hsecond
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

section Executions

variable (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ)
variable (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)

noncomputable def bodyInTime (base : K → List Bool) (a r : Nat) (token : Bool) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (hr : base (slots 1) = r.bits)
    (ht : base (slots 9) = token :: tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨some (labels .guard), clean ambient,
        Function.update (Function.update base (slots 9) tally) (slots 1) (a * r).bits⟩)
      (bodyBudget a r) := by
  have hd (i j : Fin 11) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let bt := Function.update base (slots 9) tally
  let bm := Function.update bt (slots 2) (a * r).bits
  let bc := Function.update bm (slots 1) []
  let bv := Function.update (Function.update bc (slots 2) []) (slots 10) (a * r).bits.reverse
  let done := Function.update bt (slots 1) (a * r).bits
  have h2 := hw 2 (by decide) (by decide)
  have h10 := hw 10 (by decide) (by decide)
  have guardRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change some (TM2.stepAux (p (labels .guard)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, clean, BinaryAddMachine.state, ht, bt]
  have ms0 : mulSlots slots 0 = slots 0 := rfl
  have ms1 : mulSlots slots 1 = slots 1 := rfl
  have ms2 : mulSlots slots 2 = slots 2 := rfl
  have hma : bt ((mulSlots slots) 0) = a.bits := by
    simpa [ms0, bt, hd 0 9 (by decide)] using ha
  have hmr : bt ((mulSlots slots) 1) = r.bits := by
    simpa [ms1, bt, hd 1 9 (by decide)] using hr
  have hmw : ∀ i : Fin 9, 3 ≤ i.val → bt ((mulSlots slots) i) = [] := by
    intro i hi
    let j : Fin 11 := ⟨i.val, by omega⟩
    have hjval : j.val = i.val := rfl
    have hj9 : j.val ≠ 9 := by rw [hjval]; omega
    have hj : j ≠ 9 := by
      intro h
      apply hj9
      exact congrArg Fin.val h
    change bt (slots j) = []
    simpa [bt, hd j 9 hj] using hw j (by rw [hjval]; omega) hj9
  have mulRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩
      (some ⟨some (labels .clearAccumulator), clean ambient, bm⟩)
      (BinaryMulMachine.timePolynomial.eval (a.size + r.size)) := by
    have run := BinaryMulMachine.multiplyNatInPolynomialTime (mulSlots slots)
      (fun phase => labels (.multiply phase)) (some (labels .clearAccumulator)) p
      (fun phase => atLabels (.multiply phase)) bt a r hma hmr hmw ambient
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩
      (some ⟨some (labels .clearAccumulator), clean ambient,
        Function.update bt (slots 2) ((a * r).bits ++ bt (slots 2))⟩)
      (BinaryMulMachine.timePolynomial.eval (a.size + r.size)) at run
    have hbt2 : bt (slots 2) = [] := by simp [bt, hd 2 9 (by decide), h2]
    simpa only [hbt2, List.append_nil] using run
  have clearRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .clearAccumulator), clean ambient, bm⟩
      (some ⟨some (labels .reverseProduct), clean ambient, bc⟩) (r.size + 1) := by
    have run := MachineDrain.drainInTime (slots 1) (labels .clearAccumulator)
      (some (labels .reverseProduct)) p (atLabels .clearAccumulator) bm
      ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, bc, bm, bt, hd 1 2 (by decide),
      hd 1 9 (by decide), hr, Nat.size_eq_bits_len] using run
  have reverseRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .reverseProduct), clean ambient, bc⟩
      (some ⟨some (labels .restoreAccumulator), clean ambient, bv⟩)
      ((a * r).size + 1) := by
    have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 2) (slots 10) (hd 2 10 (by decide)) id false
      (labels .reverseProduct) (some (labels .restoreAccumulator)) p
      (by simpa only [instruction] using atLabels .reverseProduct) bc ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, tapesAt, bv, bc, bm, bt,
      hd 2 1 (by decide), hd 10 1 (by decide), hd 10 2 (by decide),
      hd 10 9 (by decide), h10, Nat.size_eq_bits_len] using run
  have restoreTape : tapesAt (slots 10) (slots 1) bv []
      ((bv (slots 10)).reverse.map id ++ bv (slots 1)) = done := by
    funext k
    by_cases h1 : k = slots 1
    · subst k
      simp [tapesAt, bv, bc, bm, bt, done, hd 1 10 (by decide), hd 1 2 (by decide)]
    · by_cases h2k : k = slots 2
      · subst k
        simp [tapesAt, bv, bc, bm, bt, done, hd 2 1 (by decide), hd 2 10 (by decide),
          hd 2 9 (by decide), h2]
      · by_cases h10k : k = slots 10
        · subst k
          simp [tapesAt, bv, bc, bm, bt, done, hd 10 1 (by decide),
            hd 10 9 (by decide), h10]
        · simp [tapesAt, bv, bc, bm, done, h1, h2k, h10k]
  have restoreRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restoreAccumulator), clean ambient, bv⟩
      (some ⟨some (labels .guard), clean ambient, done⟩) ((a * r).size + 1) := by
    have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 10) (slots 1) (hd 10 1 (by decide)) id false
      (labels .restoreAccumulator) (some (labels .guard)) p
      (by simpa only [instruction] using atLabels .restoreAccumulator) bv ((ambient, false), none) none
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restoreAccumulator), clean ambient, bv⟩
      (some ⟨some (labels .guard), clean ambient,
        tapesAt (slots 10) (slots 1) bv []
          ((bv (slots 10)).reverse.map id ++ bv (slots 1))⟩)
      ((bv (slots 10)).length + 1) at run
    rw [restoreTape] at run
    have hword : bv (slots 10) = (a * r).bits.reverse := by simp [bv]
    simpa only [hword, List.length_reverse, Nat.size_eq_bits_len] using run
  exact appendRuns _ (appendRuns _ (appendRuns _ (appendRuns _ guardRun mulRun) clearRun)
    reverseRun) restoreRun

noncomputable def loopInTime (base : K → List Bool) (a r : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (hr : base (slots 1) = r.bits)
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1)
          (a ^ tally.length * r).bits⟩) (loopBudget a r tally) := by
  induction tally generalizing base r with
  | nil =>
      refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
      change some (TM2.stepAux (p (labels .guard)) _ _) = _
      rw [atLabels]
      have hself : Function.update (Function.update base (slots 9) []) (slots 1) r.bits =
          Function.update base (slots 9) [] := by
        have hd : slots 1 ≠ slots 9 := slots.injective.ne (by decide)
        have hs : (Function.update base (slots 9) []) (slots 1) = r.bits := by simp [hd, hr]
        rw [← hs, Function.update_eq_self]
      cases exit <;> simp [instruction, BinaryAddMachine.finish, BinaryAddMachine.exitAt,
        clean, BinaryAddMachine.state, TM2.stepAux, ht, hself]
  | cons token tally ih =>
      let next := Function.update (Function.update base (slots 9) tally) (slots 1) (a * r).bits
      have hd (i j : Fin 11) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
      have hna : next (slots 0) = a.bits := by
        simp [next, hd 0 1 (by decide), hd 0 9 (by decide), ha]
      have hnr : next (slots 1) = (a * r).bits := by simp [next]
      have hnt : next (slots 9) = tally := by simp [next, hd 9 1 (by decide)]
      have hnw : Workspace slots next := by
        intro i hi hi9
        have hi1 : i ≠ 1 := by intro h; have := congrArg Fin.val h; omega
        have hi9' : i ≠ 9 := by intro h; exact hi9 (congrArg Fin.val h)
        simp [next, hd i 1 hi1, hd i 9 hi9', hw i hi hi9]
      have first := bodyInTime slots labels exit p atLabels base a r token tally ha hr ht hw ambient
      have second := ih next (a * r) hna hnr hnt hnw
      have joined := appendRuns _ first second
      have hvalue : a ^ tally.length * (a * r) = a ^ (token :: tally).length * r := by
        simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hfinal : Function.update (Function.update next (slots 9) []) (slots 1)
          (a ^ tally.length * (a * r)).bits =
          Function.update (Function.update base (slots 9) []) (slots 1)
            (a ^ (token :: tally).length * r).bits := by
        funext k
        by_cases h1 : k = slots 1
        · subst k; simp [hvalue]
        · by_cases h9 : k = slots 9
          · subst k; simp [hd 9 1 (by decide)]
          · simp [next, h1, h9]
      simpa only [loopBudget, hfinal] using joined

noncomputable def powerInTime (base : K → List Bool) (a : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (outputEmpty : base (slots 1) = [])
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits⟩)
      (1 + loopBudget a 1 tally) := by
  let initial := Function.update base (slots 1) [true]
  have hd (i j : Fin 11) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have start : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize), clean ambient, base⟩
      (some ⟨some (labels .guard), clean ambient, initial⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change some (TM2.stepAux (p (labels .initialize)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, clean, BinaryAddMachine.state, outputEmpty, initial]
  have hai : initial (slots 0) = a.bits := by simp [initial, hd 0 1 (by decide), ha]
  have hri : initial (slots 1) = (1 : Nat).bits := by simp [initial]
  have hti : initial (slots 9) = tally := by simp [initial, hd 9 1 (by decide), ht]
  have hwi : Workspace slots initial := by
    intro i hi hi9
    have hi1 : i ≠ 1 := by intro h; have := congrArg Fin.val h; omega
    simp [initial, hd i 1 hi1, hw i hi hi9]
  have run := loopInTime slots labels exit p atLabels initial a 1 tally hai hri hti hwi ambient
  have hfinal : Function.update (Function.update initial (slots 9) []) (slots 1)
      (a ^ tally.length * 1).bits =
      Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits := by
    funext k
    by_cases h1 : k = slots 1
    · subst k; simp
    · by_cases h9 : k = slots 9
      · subst k; simp [hd 9 1 (by decide)]
      · simp [initial, h1, h9]
  simpa only [hfinal] using appendRuns _ start run

end Executions

noncomputable def perIteration (width : Nat) : Nat :=
  BinaryMulMachine.timePolynomial.eval (2 * width) + 3 * width + 5

theorem loopBudget_le (a r : Nat) (tally : List Bool) (width : Nat)
    (ha : a.size ≤ width) (hr : r.size + tally.length * a.size ≤ width) :
    loopBudget a r tally ≤ (tally.length + 1) * perIteration width := by
  induction tally generalizing r with
  | nil => simp [loopBudget, perIteration]
  | cons token tally ih =>
      have hp := BinaryArithmetic.size_mul_le a r
      have hnext : (a * r).size + tally.length * a.size ≤ width := by
        simp only [List.length_cons, Nat.add_mul] at hr
        omega
      have hbound := ih (a * r) hnext
      have hrs : r.size ≤ width := by omega
      have hps : (a * r).size ≤ width := by omega
      have hm := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
        (show a.size + r.size ≤ 2 * width by omega)
      have hb : bodyBudget a r ≤ perIteration width := by
        unfold bodyBudget perIteration
        omega
      simp only [loopBudget, List.length_cons]
      nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X + Polynomial.C 2) ^ 5

theorem budget_le_timePolynomial (a : Nat) (tally : List Bool) :
    1 + loopBudget a 1 tally ≤ timePolynomial.eval (a.size + tally.length) := by
  let width := (a.size + tally.length + 2) ^ 2
  have hs : 1 ≤ a.size + tally.length + 2 := by omega
  have hsq : a.size + tally.length + 2 ≤ width := le_self_pow hs (by decide)
  have hw1 : 1 ≤ width := hs.trans hsq
  have ha : a.size ≤ width := (show a.size ≤ a.size + tally.length + 2 by omega).trans hsq
  have hr : (1 : Nat).size + tally.length * a.size ≤ width := by
    simp only [Nat.size_one]
    dsimp [width]
    nlinarith
  have hloop := loopBudget_le a 1 tally width ha hr
  have hper : perIteration width ≤ 64 * width ^ 2 := by
    simp only [perIteration, BinaryMulMachine.timePolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hcount : tally.length + 1 ≤ a.size + tally.length + 2 := by omega
  have hmul := Nat.mul_le_mul hcount hper
  have hfull := hloop.trans hmul
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  dsimp [width] at hfull
  have hs5 : 1 ≤ (a.size + tally.length + 2) ^ 5 := hs.trans (le_self_pow hs (by decide))
  nlinarith [hs5]

noncomputable def powerInPolynomialTime (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (outputEmpty : base (slots 1) = [])
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits⟩)
      (timePolynomial.eval (a.size + tally.length)) := by
  let run := powerInTime slots labels exit p atLabels base a tally ha outputEmpty ht hw ambient
  exact {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := run.steps_le_m.trans (budget_le_timePolynomial a tally)
  }

end BinPackingGap.BinaryPowerMachine

end OAI

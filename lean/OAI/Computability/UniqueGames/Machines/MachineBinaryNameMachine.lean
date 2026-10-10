import Mathlib.Data.List.Induction
import OAI.Computability.UniqueGames.Machines.MachineCompare

namespace OAI

section

namespace UniqueGamesTheorem.BinaryNameMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

/-- A specification with the same one- or two-symbol cases as the program. -/
def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

theorem steps_le (input : List Bool) : steps input ≤ input.length + 1 := by
  induction input using List.twoStepInduction with
  | nil => simp [steps]
  | singleton bit => cases bit <;> simp [steps]
  | cons_cons flag bit rest ih _ =>
      cases flag <;> simp only [steps, List.length_cons]
      · omega
      · omega

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

/-- Only the finite head and final-digit registers are inspected by branches. -/
def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

private theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source, update_destination]

/-- Total correspondence, including malformed input and its exact unread suffix. -/
theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

/-- A real timed execution; the instruction equation is the only program premise. -/
def scanInTime (input output : List Bool) (last register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, last, register), tapesAt source destination base input output⟩
      (some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩)
      (input.length + 1) where
  steps := steps input
  evals_in_steps := scanTrace source destination distinct again accepted rejected program atScan
    base ambient input output last register
  steps_le_m := steps_le input

/-- A complete framed name needs exactly one transition per digit and one for
the terminator. No transition inspects the magnitude denoted by the payload. -/
theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

/-- One concrete machine with two Boolean stacks and finite control. The two
exit labels expose acceptance to a caller; the scanner leaves them unexecuted. -/
def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := State Unit
  initialState := clean ()
  m label := if label = 0 then scan false true 0 (some 1) (some 2) else .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

/-- The bounded run instantiated with the displayed finite machine, including
its actual entry and two actual exit labels. -/
def machineInTime (input output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (0 : Fin 3), clean (), tapesAt false true (fun _ : Bool => []) input output⟩
      (some ⟨if (scanSpec input output none).accepted then some (1 : Fin 3) else some (2 : Fin 3),
        clean (), tapesAt false true (fun _ : Bool => [])
          (scanSpec input output none).remaining (scanSpec input output none).reversedPayload⟩)
      (input.length + 1) :=
  scanInTime false true (by decide) (0 : Fin 3) (some 1) (some 2) machine.m
    (by simp [machine]) (fun _ : Bool => []) () input output none none

end UniqueGamesTheorem.BinaryNameMachine

end

end OAI

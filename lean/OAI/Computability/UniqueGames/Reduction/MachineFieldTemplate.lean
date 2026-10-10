import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.MachineFieldTemplate

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

def tokenOutput (fields : Fin q → List Bool) : Token q → List Bool
  | .literal bits => bits
  | .copy j => fields j

def templateOutput (tokens : List (Token q)) (fields : Fin q → List Bool) : List Bool :=
  tokens.flatMap (tokenOutput fields)

def tokenSteps (fields : Fin q → List Bool) : Token q → Nat
  | .literal _ => 1
  | .copy j => 3 * (fields j).length + 3

def workSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (tokenSteps fields)).sum

def templateSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  workSteps tokens fields + 1

def copiedLength (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (fun t => match t with | .literal _ => 0 | .copy j => (fields j).length)).sum

inductive Label (m : Nat)
  | entry (index : Fin m)
  | scan (index : Fin m)
  | emit (index : Fin m) (symbol : Bool)
  | restore (index : Fin m)
  | done
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet (_ : K) := Bool

def reset (state : State σ) : State σ := ((state.1.1, ()), none)

@[simp] theorem reset_reset (state : State σ) : reset (reset state) = reset state := rfl

def startAt (m i : Nat) : Label m :=
  if h : i < m then .entry ⟨i, h⟩ else .done

def jump (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def identityEmit (_ : Unit) (b : Bool) : List Bool := [b]

/-- Local finite labels are placed in an arbitrary caller label space, with an
explicit continuation. Every instruction is determined by the fixed template. -/
def instruction (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (place : Label tokens.length → Λ) (exit : Option Λ) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry i => match tokens.get i with
      | .literal bits => .load reset
          (pushWord output bits (.goto fun _ => place (startAt tokens.length (i.val + 1))))
      | .copy _ => .load reset (.goto fun _ => place (.scan i))
  | .scan i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransducerCopy.scanLoop (field j) scratch ()
          (fun _ b => place (.emit i b)) (place (.restore i))
  | .emit i b => MachineTransducerCopy.emitter output (fun _ _ => ()) identityEmit
      (place (.scan i)) () b
  | .restore i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransfer.loopAt scratch (field j) id false
          (place (.restore i)) (some (place (startAt tokens.length (i.val + 1))))
  | .done => .load reset (jump exit)

/-- A standalone local program, also usable with a local continuation. -/
def program (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (exit : Option (Label tokens.length)) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) (Label tokens.length) (State σ) :=
  instruction tokens field scratch output id exit

variable [DecidableEq K]

def outputTapes (base : K → List Bool) (output : K) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem outputTapes_self (base : K → List Bool) (output : K) :
    outputTapes base output [] = base := by simp [outputTapes]

@[simp] theorem outputTapes_output (base : K → List Bool) (output : K) (bits : List Bool) :
    outputTapes base output bits output = bits.reverse ++ base output := by simp [outputTapes]

theorem outputTapes_other (base : K → List Bool) (output : K) (bits : List Bool)
    (tape : K) (different : tape ≠ output) :
    outputTapes base output bits tape = base tape := by simp [outputTapes, different]

theorem outputTapes_append (base : K → List Bool) (output : K) (first second : List Bool) :
    outputTapes (outputTapes base output first) output second =
      outputTapes base output (first ++ second) := by
  simp [outputTapes, List.reverse_append, List.append_assoc]

theorem fieldValues_outputTapes (field : Fin q → K) (output : K)
    (fieldOutput : ∀ j, field j ≠ output) (base : K → List Bool) (bits : List Bool) :
    (fun j => outputTapes base output bits (field j)) = (fun j => base (field j)) := by
  funext j
  exact outputTapes_other base output bits _ (fieldOutput j)

theorem identity_output (bits : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) identityEmit () bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [MachineTransducer.output, identityEmit, ih]

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

section Execution

variable (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
variable (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
variable (scratchOutput : scratch ≠ output)
variable (place : Label tokens.length → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction tokens field scratch output place exit label)

include atInstruction

theorem doneStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place .done), state, base⟩ =
      some ⟨exit, reset state, base⟩ := by
  change some (TM2.stepAux (P (place .done)) state base) = _
  rw [atInstruction .done]
  cases exit <;> rfl

theorem literalStep (i : Fin tokens.length) (bits : List Bool)
    (token : tokens.get i = .literal bits) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output bits⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]
  rw [stepAux_pushWord]
  rfl

theorem copySetupStep (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (.scan i)), reset state, base⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]

include fieldScratch fieldOutput scratchOutput

theorem copyTrace (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 3]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (base (field j))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (field j) scratch output (fieldScratch j) (fieldOutput j) scratchOutput
    () (fun _ _ => ()) identityEmit (place (.scan i)) (place (.restore i))
    (fun _ b => place (.emit i b)) (some (place (startAt tokens.length (i.val + 1)))) P
    (by rw [atInstruction (.scan i)]; simp only [instruction, token])
    (by intro control b; cases control; exact atInstruction (.emit i b))
    (by rw [atInstruction (.restore i)]; simp only [instruction, token])
    base scratchEmpty state.1.1 () none
  rw [show 3 * (base (field j)).length + 3 =
      (3 * (base (field j)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 2]
    (TM2.step P ⟨some (place (.entry i)), state, base⟩) = _
  rw [copySetupStep tokens field scratch output place exit P atInstruction i j token]
  simpa only [identity_output, reset, outputTapes] using copied

theorem tokenTrace (i : Fin tokens.length) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[
      tokenSteps (fun j => base (field j)) (tokens.get i)]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (tokenOutput (fun j => base (field j)) (tokens.get i))⟩ := by
  cases token : tokens.get i with
  | literal bits =>
      simpa only [token, tokenSteps, tokenOutput, Function.iterate_one,
        MachineComposition.advance_some] using
        literalStep tokens field scratch output place exit P atInstruction i bits token base state
  | copy j =>
      simpa only [token, tokenSteps, tokenOutput] using
        copyTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
          atInstruction i j token base scratchEmpty state

private theorem suffixTrace (remaining : Nat) :
    ∀ (i : Nat), i + remaining = tokens.length →
      ∀ (base : K → List Bool) (_scratchEmpty : base scratch = []) (state : State σ),
        (MachineComposition.advance (TM2.step P))^[
          workSteps (tokens.drop i) (fun j => base (field j)) + 1]
          (some ⟨some (place (startAt tokens.length i)), state, base⟩) =
          some ⟨exit, reset state, outputTapes base output
            (templateOutput (tokens.drop i) (fun j => base (field j)))⟩ := by
  induction remaining with
  | zero =>
      intro i hi base _scratchEmpty state
      have heq : i = tokens.length := by omega
      subst i
      simpa [startAt, workSteps, templateOutput, MachineComposition.advance_some] using
        doneStep tokens field scratch output place exit P atInstruction base state
  | succ remaining ih =>
      intro i hi base scratchEmpty state
      have hiLt : i < tokens.length := by omega
      let index : Fin tokens.length := ⟨i, hiLt⟩
      let bits := tokenOutput (fun j => base (field j)) (tokens.get index)
      let after := outputTapes base output bits
      have first := tokenTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
        place exit P atInstruction index base scratchEmpty state
      have second := ih (i + 1) (by omega) after
        (by simpa [after, outputTapes, scratchOutput] using scratchEmpty) (reset state)
      have fieldsAfter : (fun j => after (field j)) = (fun j => base (field j)) :=
        fieldValues_outputTapes field output fieldOutput base bits
      rw [fieldsAfter] at second
      have combined := chain first second
      simp only [reset_reset, after, outputTapes_append] at combined
      have dropHead : tokens.drop i = tokens.get index :: tokens.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt tokens.length i = .entry index := by
        simp [startAt, hiLt, index]
      rw [hstart, dropHead]
      simp only [templateOutput, List.flatMap_cons]
      change _ = some (⟨exit, reset state, outputTapes base output
        (bits ++ templateOutput (tokens.drop (i + 1)) (fun j => base (field j)))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ))
      convert combined using 1
      congr 1
      simp only [workSteps, List.map_cons, List.sum_cons]
      omega

/-- The complete phase is derived from concrete instruction traces. The code
placement premise identifies instructions; it assumes no whole-phase run. -/
theorem phaseTrace (base : K → List Bool) (scratchEmpty : base scratch = [])
    (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[templateSteps tokens (fun j => base (field j))]
      (some ⟨some (place (startAt tokens.length 0)), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ := by
  simpa only [Nat.zero_add, List.drop_zero, templateSteps] using
    suffixTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
      atInstruction tokens.length 0 (by omega) base scratchEmpty state

end Execution

/-- Direct execution of the emitted local finite program; its instructions are
discharged by construction rather than supplied by the caller. -/
theorem programTrace (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (exit : Option (Label tokens.length))
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step (program tokens field scratch output exit)))^[
      templateSteps tokens (fun j => base (field j))]
      (some ⟨some (startAt tokens.length 0), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ :=
  phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput id exit
    (program tokens field scratch output exit) (fun _ => rfl) base scratchEmpty state

theorem templateSteps_le (tokens : List (Token q)) (fields : Fin q → List Bool) :
    templateSteps tokens fields ≤ 3 * copiedLength tokens fields + 3 * tokens.length + 1 := by
  have workBound : workSteps tokens fields ≤
      3 * copiedLength tokens fields + 3 * tokens.length := by
    induction tokens with
    | nil => simp [workSteps, copiedLength]
    | cons token tokens ih =>
        cases token <;>
          simp only [workSteps, copiedLength, List.map_cons, List.sum_cons,
            tokenSteps, List.length_cons] at * <;> omega
  unfold templateSteps
  omega

def phaseInTime (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label tokens.length → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction tokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt tokens.length 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩)
      (3 * copiedLength tokens (fun j => base (field j)) + 3 * tokens.length + 1) where
  steps := templateSteps tokens (fun j => base (field j))
  evals_in_steps := phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := templateSteps_le tokens _

end UniqueGamesTheorem.Reduction.MachineFieldTemplate

end

end OAI

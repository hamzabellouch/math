import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine

namespace OAI

namespace BinPackingGap.MachineFieldTemplate

open Turing
open BinPackingGames.Reduction
open BinPackingGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

variable {q : Nat} {K Λ σ : Type}

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
      ∀ (base : K → List Bool) (_ : base scratch = []) (state : State σ),
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

end BinPackingGap.MachineFieldTemplate

namespace BinPackingGap.PackingOutputEmission

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGap.MachineFieldTemplate

def itemTokens : List (Token 2) := [.literal [true], .copy 0, .copy 1]

def headerTokens : List (Token 1) := [.copy 0]

def terminatorTokens : List (Token 0) := [.literal [false]]

@[simp] theorem itemTokens_length : itemTokens.length = 3 := rfl

@[simp] theorem headerTokens_length : headerTokens.length = 1 := rfl

@[simp] theorem terminatorTokens_length : terminatorTokens.length = 1 := rfl

@[simp] theorem item_template_output (fields : Fin 2 → List Bool) :
    templateOutput itemTokens fields = true :: (fields 0 ++ fields 1) := by
  simp [itemTokens, templateOutput, tokenOutput]

@[simp] theorem item_template_steps (fields : Fin 2 → List Bool) :
    templateSteps itemTokens fields = 3 * ((fields 0).length + (fields 1).length) + 8 := by
  simp [itemTokens, templateSteps, workSteps, tokenSteps]
  omega

@[simp] theorem item_copied_length (fields : Fin 2 → List Bool) :
    copiedLength itemTokens fields = (fields 0).length + (fields 1).length := by
  simp [itemTokens, copiedLength]

@[simp] theorem header_template_output (fields : Fin 1 → List Bool) :
    templateOutput headerTokens fields = fields 0 := by
  simp [headerTokens, templateOutput, tokenOutput]

@[simp] theorem header_template_steps (fields : Fin 1 → List Bool) :
    templateSteps headerTokens fields = 3 * (fields 0).length + 4 := by
  simp [headerTokens, templateSteps, workSteps, tokenSteps]

@[simp] theorem terminator_template_output (fields : Fin 0 → List Bool) :
    templateOutput terminatorTokens fields = [false] := by
  simp [terminatorTokens, templateOutput, tokenOutput]

@[simp] theorem terminator_template_steps (fields : Fin 0 → List Bool) :
    templateSteps terminatorTokens fields = 2 := by
  simp [terminatorTokens, templateSteps, workSteps, tokenSteps]

theorem item_output_eq_binary_cons (numerator denominator : ℕ) (rest : RawInstance) :
    (true :: (BinaryEncoding.natBits numerator ++ BinaryEncoding.natBits denominator)) ++
        BinaryEncoding.rawInstanceBits rest =
      BinaryEncoding.rawInstanceBits ((numerator, denominator) :: rest) := by
  simp [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
    BinaryEncoding.pairBits, List.append_assoc]

variable {K Λ σ : Type} [DecidableEq K]

def itemProgram (field : Fin 2 → K) (scratch output : K) (exit : Option (Label 3)) :
    Label 3 → TM2.Stmt (Alphabet (K := K)) (Label 3) (State σ) :=
  program itemTokens field scratch output exit

def headerProgram (field : Fin 1 → K) (scratch output : K) (exit : Option (Label 1)) :
    Label 1 → TM2.Stmt (Alphabet (K := K)) (Label 1) (State σ) :=
  program headerTokens field scratch output exit

def terminatorProgram (scratch output : K) (exit : Option (Label 1)) :
    Label 1 → TM2.Stmt (Alphabet (K := K)) (Label 1) (State σ) :=
  program terminatorTokens Fin.elim0 scratch output exit

theorem itemPhaseTrace
    (field : Fin 2 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label 3 → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction itemTokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[
      3 * ((base (field 0)).length + (base (field 1)).length) + 8]
      (some ⟨some (place (startAt 3 0)), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (true :: (base (field 0) ++ base (field 1)))⟩ := by
  simpa only [item_template_steps, item_template_output, itemTokens_length] using
    phaseTrace itemTokens field scratch output fieldScratch fieldOutput scratchOutput
      place exit P atInstruction base scratchEmpty state

def itemPhaseInTime
    (field : Fin 2 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label 3 → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction itemTokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt 3 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (true :: (base (field 0) ++ base (field 1)))⟩)
      (3 * ((base (field 0)).length + (base (field 1)).length) + 8) where
  steps := 3 * ((base (field 0)).length + (base (field 1)).length) + 8
  evals_in_steps := itemPhaseTrace field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := le_rfl

def itemPhaseInTimeCoarse
    (field : Fin 2 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label 3 → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction itemTokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt 3 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (true :: (base (field 0) ++ base (field 1)))⟩)
      (3 * ((base (field 0)).length + (base (field 1)).length) + 10) := by
  let run := itemPhaseInTime field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  have h := run.steps_le_m
  omega

theorem itemProgramTrace
    (field : Fin 2 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (exit : Option (Label 3))
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step (itemProgram field scratch output exit)))^[
      3 * ((base (field 0)).length + (base (field 1)).length) + 8]
      (some ⟨some (startAt 3 0), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (true :: (base (field 0) ++ base (field 1)))⟩ := by
  simpa only [itemProgram, item_template_steps, item_template_output, itemTokens_length] using
    programTrace itemTokens field scratch output fieldScratch fieldOutput scratchOutput
      exit base scratchEmpty state

theorem item_fields_preserved (field : Fin 2 → K) (output : K)
    (fieldOutput : ∀ j, field j ≠ output) (base : K → List Bool) (j : Fin 2) :
    outputTapes base output (true :: (base (field 0) ++ base (field 1))) (field j) =
      base (field j) :=
  outputTapes_other base output _ (field j) (fieldOutput j)

theorem item_scratch_restored (field : Fin 2 → K) (scratch output : K)
    (scratchOutput : scratch ≠ output) (base : K → List Bool) (h : base scratch = []) :
    outputTapes base output (true :: (base (field 0) ++ base (field 1))) scratch = [] := by
  rw [outputTapes_other base output _ scratch scratchOutput, h]

theorem item_accumulator (field : Fin 2 → K) (output : K) (base : K → List Bool) :
    outputTapes base output (true :: (base (field 0) ++ base (field 1))) output =
      (true :: (base (field 0) ++ base (field 1))).reverse ++ base output :=
  outputTapes_output base output _

theorem framed_item_steps (numerator denominator : ℕ) :
    3 * ((BinaryEncoding.natBits numerator).length +
      (BinaryEncoding.natBits denominator).length) + 8 =
        6 * (Nat.size numerator + Nat.size denominator) + 14 := by
  simp only [BinaryEncoding.natBits_length]
  omega

theorem headerPhaseTrace
    (field : Fin 1 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label 1 → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction headerTokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[3 * (base (field 0)).length + 4]
      (some ⟨some (place (startAt 1 0)), state, base⟩) =
      some ⟨exit, reset state, outputTapes base output (base (field 0))⟩ := by
  simpa only [header_template_steps, header_template_output, headerTokens_length] using
    phaseTrace headerTokens field scratch output fieldScratch fieldOutput scratchOutput
      place exit P atInstruction base scratchEmpty state

theorem headerProgramTrace
    (field : Fin 1 → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (exit : Option (Label 1))
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step (headerProgram field scratch output exit)))^[
      3 * (base (field 0)).length + 4]
      (some ⟨some (startAt 1 0), state, base⟩) =
      some ⟨exit, reset state, outputTapes base output (base (field 0))⟩ := by
  simpa only [headerProgram, header_template_steps, header_template_output, headerTokens_length] using
    programTrace headerTokens field scratch output fieldScratch fieldOutput scratchOutput
      exit base scratchEmpty state

theorem terminatorPhaseTrace (scratch output : K) (scratchOutput : scratch ≠ output)
    (place : Label 1 → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction terminatorTokens Fin.elim0 scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[2]
      (some ⟨some (place (startAt 1 0)), state, base⟩) =
      some ⟨exit, reset state, outputTapes base output [false]⟩ := by
  simpa only [terminator_template_steps, terminator_template_output, terminatorTokens_length] using
    phaseTrace terminatorTokens Fin.elim0 scratch output (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) scratchOutput place exit P atInstruction base scratchEmpty state

theorem terminatorProgramTrace (scratch output : K) (scratchOutput : scratch ≠ output)
    (exit : Option (Label 1)) (base : K → List Bool) (scratchEmpty : base scratch = [])
    (state : State σ) :
    (MachineComposition.advance (TM2.step (terminatorProgram scratch output exit)))^[2]
      (some ⟨some (startAt 1 0), state, base⟩) =
      some ⟨exit, reset state, outputTapes base output [false]⟩ := by
  simpa only [terminatorProgram, terminator_template_steps, terminator_template_output,
    terminatorTokens_length] using
    programTrace terminatorTokens Fin.elim0 scratch output (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) scratchOutput exit base scratchEmpty state

end BinPackingGap.PackingOutputEmission

namespace BinPackingGap.PackingPoolMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGap.MachineFieldTemplate
open MachineUnaryCounter (counterTapes)

inductive Label
  | guard
  | emit (localLabel : BinPackingGap.MachineFieldTemplate.Label 3)
  | done
  deriving DecidableEq, Fintype

variable {K Λ A : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some l => .goto (fun _ => l)

def instruction (field : Fin 2 → K) (scratch output counter : K)
    (place : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard => MachineUnaryCounter.guard counter
      (place (.emit (startAt 3 0))) (place .done)
  | .emit l => BinPackingGap.MachineFieldTemplate.instruction
      PackingOutputEmission.itemTokens field scratch output
      (fun l => place (.emit l)) (some (place .guard)) l
  | .done => finish exit

def repeatWord (word : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => repeatWord word n ++ word

@[simp] theorem repeatWord_zero (word : List Bool) : repeatWord word 0 = [] := rfl

@[simp] theorem repeatWord_succ (word : List Bool) (n : Nat) :
    repeatWord word (n + 1) = repeatWord word n ++ word := rfl

theorem repeatWord_length (word : List Bool) (n : Nat) :
    (repeatWord word n).length = n * word.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.add_mul]

def record (numerator denominator : List Bool) : List Bool :=
  true :: (numerator ++ denominator)

def bodySteps (numerator denominator : List Bool) : Nat :=
  3 * (numerator.length + denominator.length) + 8

def steps (n : Nat) (numerator denominator : List Bool) : Nat :=
  n * (bodySteps numerator denominator + 1) + 1

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem poolTrace
    (field : Fin 2 → K) (scratch output counter : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (fieldCounter : ∀ j, field j ≠ counter)
    (scratchOutput : scratch ≠ output) (scratchCounter : scratch ≠ counter)
    (outputCounter : output ≠ counter)
    (place : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atInstruction : ∀ l, P (place l) = instruction field scratch output counter place exit l)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (numerator denominator : List Bool)
    (numWord : base (field 0) = numerator) (denWord : base (field 1) = denominator)
    (ambient : A) (suffix : List Bool) (n : Nat) :
    (MachineComposition.advance (TM2.step P))^[steps n numerator denominator]
      (some ⟨some (place .guard), ((ambient, ()), none),
        counterTapes counter base n suffix⟩) =
      some ⟨some (place .done), ((ambient, ()), none),
        counterTapes counter
          (Function.update base output
            (repeatWord (record numerator denominator).reverse n ++ base output))
          0 suffix⟩ := by
  induction n generalizing base with
  | zero =>
      have h := MachineUnaryCounter.guardTrace_zero counter (place .guard)
        (place (.emit (startAt 3 0))) (place .done) P (atInstruction .guard)
        base suffix (ambient, ()) none
      simpa [steps, repeatWord] using h
  | succ n ih =>
      let next := Function.update base output
        ((record numerator denominator).reverse ++ base output)
      have nextScratch : next scratch = [] := by
        simp [next, scratchOutput, scratchEmpty]
      have nextNum : next (field 0) = numerator := by
        simp [next, fieldOutput 0, numWord]
      have nextDen : next (field 1) = denominator := by
        simp [next, fieldOutput 1, denWord]
      have guardRun := MachineUnaryCounter.guardTrace_succ counter (place .guard)
        (place (.emit (startAt 3 0))) (place .done) P (atInstruction .guard)
        base n suffix (ambient, ()) none
      have bodyRun := PackingOutputEmission.itemPhaseTrace field scratch output
        fieldScratch fieldOutput scratchOutput (fun l => place (.emit l))
        (some (place .guard)) P (fun l => atInstruction (.emit l))
        (counterTapes counter base n suffix)
        (by simp [counterTapes, scratchCounter, scratchEmpty]) ((ambient, ()), none)
      have bodyOutput :
          outputTapes (counterTapes counter base n suffix) output
            (true :: (counterTapes counter base n suffix (field 0) ++
              counterTapes counter base n suffix (field 1))) =
            counterTapes counter next n suffix := by
        funext k
        by_cases hc : k = counter
        · subst k
          simp [outputTapes, counterTapes, next, outputCounter.symm]
        · by_cases ho : k = output
          · subst k
            simp [outputTapes, counterTapes, next, outputCounter,
              fieldCounter 0, fieldCounter 1, numWord, denWord, record]
          · simp [outputTapes, counterTapes, next, hc, ho]
      have bodyRun' :
          (MachineComposition.advance (TM2.step P))^[bodySteps numerator denominator]
            (some ⟨some (place (.emit (startAt 3 0))), ((ambient, ()), none),
              counterTapes counter base n suffix⟩) =
            some ⟨some (place .guard), ((ambient, ()), none),
              counterTapes counter next n suffix⟩ := by
        rw [bodyOutput] at bodyRun
        simpa only [MachineUnaryCounter.counterTapes_other counter (field 0)
          (fieldCounter 0), MachineUnaryCounter.counterTapes_other counter (field 1)
          (fieldCounter 1), numWord, denWord, bodySteps, reset] using bodyRun
      have restRun := ih next nextScratch nextNum nextDen
      have allRun := joinTrace (joinTrace guardRun bodyRun') restRun
      have stepEq : 1 + bodySteps numerator denominator + steps n numerator denominator =
          steps (n + 1) numerator denominator := by
        simp [steps, Nat.add_mul]
        omega
      rw [stepEq] at allRun
      convert allRun using 1
      congr 2
      funext k
      by_cases hc : k = counter
      · subst k; simp [counterTapes]
      · by_cases ho : k = output
        · subst k
          simp [counterTapes, next, outputCounter, repeatWord_succ, List.append_assoc]
        · simp [counterTapes, next, hc, ho]

def poolInTime
    (field : Fin 2 → K) (scratch output counter : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (fieldCounter : ∀ j, field j ≠ counter)
    (scratchOutput : scratch ≠ output) (scratchCounter : scratch ≠ counter)
    (outputCounter : output ≠ counter)
    (place : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atInstruction : ∀ l, P (place l) = instruction field scratch output counter place exit l)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (numerator denominator : List Bool)
    (numWord : base (field 0) = numerator) (denWord : base (field 1) = denominator)
    (ambient : A) (suffix : List Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place .guard), ((ambient, ()), none), counterTapes counter base n suffix⟩
      (some ⟨exit, ((ambient, ()), none), counterTapes counter
        (Function.update base output
          (repeatWord (record numerator denominator).reverse n ++ base output)) 0 suffix⟩)
      (n * (3 * (numerator.length + denominator.length) + 9) + 2) := by
  let finalTapes := counterTapes counter
    (Function.update base output
      (repeatWord (record numerator denominator).reverse n ++ base output)) 0 suffix
  have h := poolTrace field scratch output counter fieldScratch fieldOutput fieldCounter
    scratchOutput scratchCounter outputCounter place exit P atInstruction base scratchEmpty
    numerator denominator numWord denWord ambient suffix n
  have finishRun : (MachineComposition.advance (TM2.step P))^[1]
      (some ⟨some (place .done), ((ambient, ()), none), finalTapes⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes⟩ := by
    simp only [Function.iterate_one, MachineComposition.advance_some, TM2.step]
    rw [atInstruction .done]
    cases exit <;> rfl
  refine {
    steps := steps n numerator denominator + 1
    evals_in_steps := joinTrace h finishRun
    steps_le_m := ?_
  }
  simp [steps, bodySteps]

end BinPackingGap.PackingPoolMachine

end OAI

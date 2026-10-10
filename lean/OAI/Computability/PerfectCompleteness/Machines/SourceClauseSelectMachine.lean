import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Machines.SourceClauseReaderMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.UnaryBlockCopyMachine
import OAI.Computability.PerfectCompleteness.Machines.UnaryBlockSkipMachine

namespace OAI


namespace PerfectCompleteness.SourceClauseSelectMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def steps {n : Nat} (first : Nat) : List (Target.Clause n) → Nat → Nat
  | [], _ => 0
  | clause :: _, 0 => 1 + (SourceOccurrenceEncoding.recordBits first clause).length
  | clause :: clauses, offset + 1 =>
      1 + (SourceOccurrenceEncoding.recordBits first clause).length + steps (first + 1) clauses offset

theorem steps_le {n : Nat} (clauses : List (Target.Clause n)) (first offset : Nat)
    (bound : offset < clauses.length) :
    steps first clauses offset ≤ (SourceOccurrenceEncoding.body first clauses).length + offset + 1 := by
  induction offset generalizing clauses first with
  | zero =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          simp only [steps, SourceOccurrenceEncoding.body_cons, List.length_append]
          omega
  | succ offset ih =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have tail := ih clauses (first + 1) (by
            simp only [List.length_cons] at bound
            omega)
          simp only [steps, SourceOccurrenceEncoding.body_cons, List.length_append]
          omega

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean (ambient : A) : State A := (ambient, none)

inductive Label
  | guard
  | skip (slot : Fin 7)
  | index (slot : Fin 1)
  | copy (slot : Fin 6)
  deriving DecidableEq, Fintype

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def instruction (tape : Fin 3 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (tape 1) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isNone)
          (finish (some (labels (.index 0))))
          (.branch (fun state => state.2.getD false)
            (finish (some (labels (.skip 0)))) (finish rejected)))
  | .skip slot => UnaryBlockSkipMachine.instruction (tape 0) (labels (.skip slot))
      (UnaryBlockSkipMachine.nextField (fun slot => labels (.skip slot))
        (some (labels .guard)) slot) rejected
  | .index slot => UnaryBlockSkipMachine.instruction (tape 0) (labels (.index slot))
      (UnaryBlockSkipMachine.nextField (fun slot => labels (.index slot))
        (some (labels (.copy 0))) slot) rejected
  | .copy slot => UnaryBlockCopyMachine.instruction (tape 0) (tape 2) (labels (.copy slot))
      (UnaryBlockCopyMachine.nextField (fun slot => labels (.copy slot)) done slot) rejected

def selectTapes (tape : Fin 3 → K) (base : K → List Bool) (input : List Bool)
    (offset : Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base (tape 0) input)
    (tape 1) (List.replicate offset true)) (tape 2) output

theorem selectTapes_input (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (offset : Nat) (output : List Bool) :
    selectTapes tape base input offset output (tape 0) = input := by
  have hd (i j : Fin 3) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [selectTapes, hd]

theorem selectTapes_offset (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (offset : Nat) (output : List Bool) :
    selectTapes tape base input offset output (tape 1) = List.replicate offset true := by
  have hd (i j : Fin 3) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [selectTapes, hd]

theorem selectTapes_output (tape : Fin 3 → K) (base : K → List Bool) (input : List Bool)
    (offset : Nat) (output : List Bool) :
    selectTapes tape base input offset output (tape 2) = output := by
  simp [selectTapes]

private theorem update_input (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (offset : Nat) (output : List Bool) :
    Function.update (selectTapes tape base input offset output) (tape 0) replacement =
      selectTapes tape base replacement offset output := by
  have hd (i j : Fin 3) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [selectTapes, hd]
  · simp [selectTapes, h, Function.update_apply]

private theorem update_offset (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (offset replacement : Nat) (output : List Bool) :
    Function.update (selectTapes tape base input offset output)
        (tape 1) (List.replicate replacement true) =
      selectTapes tape base input replacement output := by
  have hd (i j : Fin 3) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [selectTapes, hd]
  · simp [selectTapes, h, Function.update_apply]

private theorem update_output (tape : Fin 3 → K) (base : K → List Bool)
    (input : List Bool) (offset : Nat) (output replacement : List Bool) :
    Function.update (selectTapes tape base input offset output) (tape 2) replacement =
      selectTapes tape base input offset replacement := by
  simp [selectTapes]

private theorem tapesAt_select (tape : Fin 3 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (offset : Nat)
    (output newOutput : List Bool) :
    tapesAt (tape 0) (tape 2) (selectTapes tape base input offset output) replacement newOutput =
      selectTapes tape base replacement offset newOutput := by
  unfold tapesAt
  rw [update_input tape distinct, update_output]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 3 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem guardStep (input : List Bool) (offset : Nat) (output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), clean ambient, selectTapes tape base input (offset + 1) output⟩ =
      some ⟨some (labels (.skip 0)), clean ambient, selectTapes tape base input offset output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, clean, selectTapes_offset tape distinct,
    List.replicate_succ, update_offset tape distinct]

theorem zeroStep (input output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), clean ambient, selectTapes tape base input 0 output⟩ =
      some ⟨some (labels (.index 0)), clean ambient, selectTapes tape base input 0 output⟩ := by
  have unchanged : Function.update (selectTapes tape base input 0 output) (tape 1) [] =
      selectTapes tape base input 0 output := by
    simpa only [List.replicate_zero] using update_offset tape distinct base input 0 0 output
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, clean, selectTapes_offset tape distinct, unchanged]

theorem skipTrace {n : Nat} (first : Nat) (clause : Target.Clause n)
    (suffix : List Bool) (offset : Nat) (output : List Bool) :
    (advance (TM2.step program))^[1 + (SourceOccurrenceEncoding.recordBits first clause).length]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.recordBits first clause ++ suffix)
          (offset + 1) output⟩) =
      some ⟨some (labels .guard), clean ambient, selectTapes tape base suffix offset output⟩ := by
  let input := SourceOccurrenceEncoding.recordBits first clause ++ suffix
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient, selectTapes tape base input (offset + 1) output⟩) =
      some ⟨some (labels (.skip 0)), clean ambient, selectTapes tape base input offset output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient input offset output
  have skip := UnaryBlockSkipMachine.listTrace (count := 6) (tape 0)
    (fun slot => labels (.skip slot)) (some (labels .guard)) rejected program
    (fun slot => atLabels (.skip slot)) (selectTapes tape base input offset output) ambient
    (SourceOccurrenceEncoding.recordWords first clause) (by simp) suffix none
  simp only [update_input tape distinct] at skip
  exact joinTrace guard skip

theorem zeroTrace {n : Nat} (first : Nat) (clause : Target.Clause n)
    (suffix output : List Bool) :
    (advance (TM2.step program))^[1 + (SourceOccurrenceEncoding.recordBits first clause).length]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.recordBits first clause ++ suffix) 0 output⟩) =
      some ⟨done, clean ambient, selectTapes tape base suffix 0
        ((encodeWords (clauseWords clause)).reverse ++ output)⟩ := by
  have hd : tape 0 ≠ tape 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (distinct h)
  let input := SourceOccurrenceEncoding.recordBits first clause ++ suffix
  let clauseInput := encodeWords (clauseWords clause) ++ suffix
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient, selectTapes tape base input 0 output⟩) =
      some ⟨some (labels (.index 0)), clean ambient, selectTapes tape base input 0 output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      zeroStep tape distinct labels done rejected program atLabels base ambient input output
  have index : (advance (TM2.step program))^[(encodeWord first).length]
      (some ⟨some (labels (.index 0)), clean ambient, selectTapes tape base input 0 output⟩) =
      some ⟨some (labels (.copy 0)), clean ambient, selectTapes tape base clauseInput 0 output⟩ := by
    have h := UnaryBlockSkipMachine.listTrace (count := 0) (tape 0)
      (fun slot => labels (.index slot)) (some (labels (.copy 0))) rejected program
      (fun slot => atLabels (.index slot)) (selectTapes tape base input 0 output) ambient
      [first] (by simp) clauseInput none
    simpa only [encodeWords, List.append_nil, update_input tape distinct, input, clauseInput,
      SourceOccurrenceEncoding.recordBits_eq, List.append_assoc, clean] using h
  have copy : (advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
      (some ⟨some (labels (.copy 0)), clean ambient, selectTapes tape base clauseInput 0 output⟩) =
      some ⟨done, clean ambient, selectTapes tape base suffix 0
        ((encodeWords (clauseWords clause)).reverse ++ output)⟩ := by
    have h := UnaryBlockCopyMachine.listTrace (tape 0) (tape 2) hd
      (fun slot => labels (.copy slot)) done rejected program
      (fun slot => atLabels (.copy slot)) (selectTapes tape base clauseInput 0 output) ambient
      (clauseWords clause) (by simp) suffix output none
    simpa only [tapesAt_select tape distinct, clauseInput, clean] using h
  have full := joinTrace (joinTrace guard index) copy
  simpa only [input, SourceOccurrenceEncoding.recordBits_eq, List.length_append,
    List.append_assoc, Nat.add_assoc] using full

theorem selectTrace {n : Nat} (clauses : List (Target.Clause n)) (first offset : Nat)
    (bound : offset < clauses.length) (suffix output : List Bool) :
    (advance (TM2.step program))^[steps first clauses offset]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.body first clauses ++ suffix) offset output⟩) =
      some ⟨done, clean ambient,
        selectTapes tape base
          (SourceOccurrenceEncoding.body (first + offset + 1) (clauses.drop (offset + 1)) ++ suffix) 0
          ((encodeWords (clauseWords clauses[offset])).reverse ++ output)⟩ := by
  induction offset generalizing clauses first with
  | zero =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have h := zeroTrace tape distinct labels done rejected program atLabels base ambient
            first clause (SourceOccurrenceEncoding.body (first + 1) clauses ++ suffix) output
          simpa only [steps, SourceOccurrenceEncoding.body_cons, List.append_assoc,
            Nat.add_zero, List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero] using h
  | succ offset ih =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have tailBound : offset < clauses.length := by
            simp only [List.length_cons] at bound
            omega
          have skip := skipTrace tape distinct labels done rejected program atLabels base ambient
            first clause (SourceOccurrenceEncoding.body (first + 1) clauses ++ suffix) offset output
          have tail := ih clauses (first + 1) tailBound
          have full := joinTrace skip tail
          have address : first + 1 + offset + 1 = first + (offset + 1) + 1 := by omega
          simpa only [steps, SourceOccurrenceEncoding.body_cons, List.append_assoc,
            List.drop_succ_cons, List.getElem_cons_succ, address] using full

def selectInTime {n : Nat} (clauses : List (Target.Clause n)) (first offset : Nat)
    (bound : offset < clauses.length) (suffix output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.body first clauses ++ suffix) offset output⟩
      (some ⟨done, clean ambient,
        selectTapes tape base
          (SourceOccurrenceEncoding.body (first + offset + 1) (clauses.drop (offset + 1)) ++ suffix) 0
          ((encodeWords (clauseWords clauses[offset])).reverse ++ output)⟩)
      ((SourceOccurrenceEncoding.body first clauses).length + offset + 1) where
  steps := steps first clauses offset
  evals_in_steps := selectTrace tape distinct labels done rejected program atLabels base ambient
    clauses first offset bound suffix output
  steps_le_m := steps_le clauses first offset bound

end Program

end PerfectCompleteness.SourceClauseSelectMachine

end OAI

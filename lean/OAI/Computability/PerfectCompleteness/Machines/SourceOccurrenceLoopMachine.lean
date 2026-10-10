import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Machines.SourceClauseReaderMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.SourceOccurrenceIndexMachine
import OAI.Computability.PerfectCompleteness.Machines.UnaryBlockCopyMachine

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def bodySteps {n : Nat} (first : Nat) (clause : Target.Clause n) : Nat :=
  1 + SourceOccurrenceIndexMachine.steps first + (encodeWords (clauseWords clause)).length + 1

def steps {n : Nat} (first : Nat) : List (Target.Clause n) → Nat
  | [] => 1
  | clause :: clauses => bodySteps first clause + steps (first + 1) clauses

theorem bodySteps_le {n : Nat} (first maximum : Nat) (clause : Target.Clause n)
    (indexBound : first ≤ maximum) :
    bodySteps first clause ≤ 2 * maximum + 3 + 3 * (n + 2) + 2 := by
  have encoded := clauseBits_length_le clause
  unfold bodySteps SourceOccurrenceIndexMachine.steps
  omega

theorem steps_le {n : Nat} (first maximum : Nat) (clauses : List (Target.Clause n))
    (indexBound : first + clauses.length ≤ maximum) :
    steps first clauses ≤ clauses.length * (2 * maximum + 3 + 3 * (n + 2) + 2) + 1 := by
  induction clauses generalizing first with
  | nil => simp [steps]
  | cons clause clauses ih =>
      have head := bodySteps_le first maximum clause (by
        simp only [List.length_cons] at indexBound
        omega)
      have tail := ih (first + 1) (by
        simp only [List.length_cons] at indexBound
        omega)
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
abbrev clean (ambient : A) : State A := SourceOccurrenceIndexMachine.clean ambient

def indexMap : Fin 3 → Fin 5
  | 0 => 2
  | 1 => 3
  | 2 => 4

def indexTapes (tape : Fin 5 → K) : Fin 3 → K := fun i => tape (indexMap i)

omit [DecidableEq K] in
theorem indexTapes_injective (tape : Fin 5 → K) (distinct : Function.Injective tape) :
    Function.Injective (indexTapes tape) :=
  distinct.comp (by decide : Function.Injective indexMap)

inductive Label
  | guard
  | index (label : SourceOccurrenceIndexMachine.Label)
  | field (slot : Fin 6)
  | tally
  deriving DecidableEq, Fintype

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def instruction (tape : Fin 5 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (tape 1) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isNone) (finish done)
          (.branch (fun state => state.2.getD false)
            (finish (some (labels (.index SourceOccurrenceIndexMachine.main)))) (finish rejected)))
  | .index l => SourceOccurrenceIndexMachine.instruction (indexTapes tape)
      (fun l => labels (.index l)) (some (labels (.field 0))) l
  | .field slot => UnaryBlockCopyMachine.instruction (tape 0) (tape 4) (labels (.field slot))
      (UnaryBlockCopyMachine.nextField (fun slot => labels (.field slot))
        (some (labels .tally)) slot) rejected
  | .tally => .push (tape 2) (fun _ => true) (finish (some (labels .guard)))

def loopTapes (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) input) (tape 1) (List.replicate remaining true))
    (tape 2) (List.replicate first true)) (tape 4) output

theorem loopTapes_input (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 0) = input := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_remaining (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 1) = List.replicate remaining true := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_index (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 2) = List.replicate first true := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_scratch (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 3) = base (tape 3) := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_output (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 4) = output := by
  simp [loopTapes]

private theorem update_input (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (remaining first : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output) (tape 0) replacement =
      loopTapes tape base replacement remaining first output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_remaining (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first replacement : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output)
        (tape 1) (List.replicate replacement true) =
      loopTapes tape base input replacement first output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_index (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (remaining first replacement : Nat)
    (output : List Bool) :
    Function.update (loopTapes tape base input remaining first output)
        (tape 2) (List.replicate replacement true) =
      loopTapes tape base input remaining replacement output := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_output (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output replacement : List Bool) :
    Function.update (loopTapes tape base input remaining first output) (tape 4) replacement =
      loopTapes tape base input remaining first replacement := by
  simp [loopTapes]

private theorem tapesAt_loop (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input replacement : List Bool) (remaining first : Nat)
    (output newOutput : List Bool) :
    tapesAt (tape 0) (tape 4) (loopTapes tape base input remaining first output)
      replacement newOutput = loopTapes tape base replacement remaining first newOutput := by
  unfold tapesAt
  rw [update_input tape distinct, update_output]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 5 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem guardStep (input : List Bool) (remaining first : Nat) (output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), clean ambient,
        loopTapes tape base input (remaining + 1) first output⟩ =
      some ⟨some (labels (.index SourceOccurrenceIndexMachine.main)), clean ambient,
        loopTapes tape base input remaining first output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, clean, SourceOccurrenceIndexMachine.clean,
    loopTapes_remaining tape distinct, List.replicate_succ, update_remaining tape distinct]

theorem emptyStep (input : List Bool) (first : Nat) (output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), clean ambient, loopTapes tape base input 0 first output⟩ =
      some ⟨done, clean ambient, loopTapes tape base input 0 first output⟩ := by
  have unchanged : Function.update (loopTapes tape base input 0 first output) (tape 1) [] =
      loopTapes tape base input 0 first output := by
    simpa only [List.replicate_zero] using
      update_remaining tape distinct base input 0 first 0 output
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, clean, SourceOccurrenceIndexMachine.clean,
    loopTapes_remaining tape distinct, unchanged]

theorem tallyStep (input : List Bool) (remaining first : Nat) (output : List Bool) :
    TM2.step program
      ⟨some (labels .tally), clean ambient, loopTapes tape base input remaining first output⟩ =
      some ⟨some (labels .guard), clean ambient, loopTapes tape base input remaining (first + 1) output⟩ := by
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  simp [instruction, TM2.stepAux, clean, SourceOccurrenceIndexMachine.clean,
    loopTapes_index tape distinct, ← List.replicate_succ, update_index tape distinct]

theorem bodyTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (remaining first : Nat) (output : List Bool) (scratchEmpty : base (tape 3) = []) :
    (advance (TM2.step program))^[bodySteps first clause]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          (remaining + 1) first output⟩) =
      some ⟨some (labels .guard), clean ambient,
        loopTapes tape base suffix remaining (first + 1)
          ((SourceOccurrenceEncoding.recordBits first clause).reverse ++ output)⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let input := encodeWords (clauseWords clause) ++ suffix
  let indexOutput := (encodeWord first).reverse ++ output
  let clauseOutput := (encodeWords (clauseWords clause)).reverse ++ indexOutput
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base input (remaining + 1) first output⟩) =
      some ⟨some (labels (.index SourceOccurrenceIndexMachine.main)), clean ambient,
        loopTapes tape base input remaining first output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient
        input remaining first output
  have index := SourceOccurrenceIndexMachine.indexTrace (indexTapes tape)
    (indexTapes_injective tape distinct) (fun l => labels (.index l))
    (some (labels (.field 0))) program (fun l => atLabels (.index l))
    (loopTapes tape base input remaining first output) ambient first
    (by simp [indexTapes, indexMap, loopTapes, hd])
    (by simp [indexTapes, indexMap, loopTapes, hd, scratchEmpty])
  rw [show indexTapes tape 2 = tape 4 from rfl, loopTapes_output, update_output] at index
  have copied : (advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
      (some ⟨some (labels (.field 0)), clean ambient,
        loopTapes tape base input remaining first indexOutput⟩) =
      some ⟨some (labels .tally), clean ambient,
        loopTapes tape base suffix remaining first clauseOutput⟩ := by
    have h := UnaryBlockCopyMachine.listTrace (tape 0) (tape 4) (hd 0 4 (by decide))
      (fun slot => labels (.field slot)) (some (labels .tally)) rejected program
      (fun slot => atLabels (.field slot))
      (loopTapes tape base input remaining first indexOutput) ambient
      (clauseWords clause) (by simp) suffix indexOutput none
    simpa only [tapesAt_loop tape distinct, clean, SourceOccurrenceIndexMachine.clean,
      input, clauseOutput] using h
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient,
        loopTapes tape base suffix remaining first clauseOutput⟩) =
      some ⟨some (labels .guard), clean ambient,
        loopTapes tape base suffix remaining (first + 1) clauseOutput⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done rejected program atLabels base ambient
        suffix remaining first clauseOutput
  have full := joinTrace (joinTrace (joinTrace guard index) copied) tally
  simpa only [bodySteps, input, clauseOutput, indexOutput,
    SourceOccurrenceEncoding.recordBits_eq, List.reverse_append, List.append_assoc] using full

theorem loopTrace {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (first : Nat) (output : List Bool) (scratchEmpty : base (tape 3) = []) :
    (advance (TM2.step program))^[steps first clauses]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          clauses.length first output⟩) =
      some ⟨done, clean ambient,
        loopTapes tape base suffix 0 (first + clauses.length)
          ((SourceOccurrenceEncoding.body first clauses).reverse ++ output)⟩ := by
  induction clauses generalizing first output with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, List.flatMap_nil, encodeWords,
        List.nil_append, List.length_nil, Nat.add_zero, SourceOccurrenceEncoding.body_nil,
        List.reverse_nil] using
        emptyStep tape distinct labels done rejected program atLabels base ambient suffix first output
  | cons clause clauses ih =>
      have head := bodyTrace tape distinct labels done rejected program atLabels base ambient clause
        (encodeWords (clauses.flatMap clauseWords) ++ suffix) clauses.length first output scratchEmpty
      have tail := ih (first + 1)
        ((SourceOccurrenceEncoding.recordBits first clause).reverse ++ output)
      have full := joinTrace head tail
      have indexEq : first + 1 + clauses.length = first + (clauses.length + 1) := by omega
      simpa only [steps, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons, indexEq, SourceOccurrenceEncoding.body_cons, List.reverse_append] using full

def loopInTime {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (first maximum : Nat) (output : List Bool) (scratchEmpty : base (tape 3) = [])
    (indexBound : first + clauses.length ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .guard), clean ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          clauses.length first output⟩
      (some ⟨done, clean ambient,
        loopTapes tape base suffix 0 (first + clauses.length)
          ((SourceOccurrenceEncoding.body first clauses).reverse ++ output)⟩)
      (clauses.length * (2 * maximum + 3 + 3 * (n + 2) + 2) + 1) where
  steps := steps first clauses
  evals_in_steps := loopTrace tape distinct labels done rejected program atLabels base ambient
    clauses suffix first output scratchEmpty
  steps_le_m := steps_le first maximum clauses indexBound

end Program

end PerfectCompleteness.SourceOccurrenceLoopMachine

end OAI

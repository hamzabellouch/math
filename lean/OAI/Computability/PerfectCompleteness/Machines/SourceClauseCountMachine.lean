import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Machines.SourceClauseReaderMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.UnaryBlockSkipMachine
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI


namespace PerfectCompleteness.SourceClauseCountMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean {A : Type} (ambient : A) : State A := (ambient, none)

inductive Label
  | tableOut | tableBack
  | skip (slot : Fin 1)
  | readCount | drain
  deriving DecidableEq, Fintype

def main : Label := .tableOut

def steps (formula : Formula) : Nat :=
  2 * ((SourceOccurrenceEncoding.bits formula).length + 1) +
    (formula.variables + 1) + (formula.clauses.length + 1) +
    ((SourceOccurrenceEncoding.body 0 formula.clauses).length + 1)

theorem steps_eq (formula : Formula) :
    steps formula = 3 * ((SourceOccurrenceEncoding.bits formula).length + 1) := by
  have tableLength : (SourceOccurrenceEncoding.bits formula).length =
      formula.variables + formula.clauses.length + 2 +
        (SourceOccurrenceEncoding.body 0 formula.clauses).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  unfold steps
  omega

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 4 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .tableOut => loopAt (tape 0) (tape 2) id false
      (labels .tableOut) (some (labels .tableBack))
  | .tableBack => MachineCopy.forkLoop (tape 2) (tape 0) (tape 1) false
      (labels .tableBack) (some (labels (.skip 0)))
  | .skip slot => UnaryBlockSkipMachine.instruction (tape 1) (labels (.skip slot))
      (UnaryBlockSkipMachine.nextField (fun slot => labels (.skip slot))
        (some (labels .readCount)) slot) rejected
  | .readCount => Hastad.SourceMachine.fieldLoop (tape 1) (tape 3)
      (labels .readCount) (some (labels .drain))
  | .drain => MachineDrain.drain (tape 1) (labels .drain) done

def workTapes (tape : Fin 4 → K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 1) input) (tape 3) output

theorem workTapes_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input output : List Bool) :
    workTapes tape base input output (tape 1) = input := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  simp [workTapes, different]

@[simp] theorem workTapes_output (tape : Fin 4 → K) (base : K → List Bool)
    (input output : List Bool) : workTapes tape base input output (tape 3) = output := by
  simp [workTapes]

private theorem update_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (workTapes tape base input output) (tape 1) replacement =
      workTapes tape base replacement output := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [workTapes, different]
  · simp [workTapes, h, Function.update_apply]

theorem workTapes_empty (tape : Fin 4 → K) (base : K → List Bool) (output : List Bool)
    (copyEmpty : base (tape 1) = []) :
    workTapes tape base [] output = Function.update base (tape 3) output := by
  have copySelf := Function.update_eq_self (tape 1) base
  rw [copyEmpty] at copySelf
  simp only [workTapes, copySelf]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem copyTrace (table output : List Bool)
    (tableWord : base (tape 0) = table) (scratchEmpty : base (tape 2) = []) :
    (advance (TM2.step program))^[2 * (table.length + 1)]
      (some ⟨some (labels .tableOut), clean ambient, workTapes tape base [] output⟩) =
      some ⟨some (labels (.skip 0)), clean ambient, workTapes tape base table output⟩ := by
  have hd (i j : Fin 4) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have source : workTapes tape base [] output (tape 0) = table := by
    simp [workTapes, hd, tableWord]
  have scratch : workTapes tape base [] output (tape 2) = [] := by
    simp [workTapes, hd, scratchEmpty]
  have run := MachineCopy.copyTrace (tape 0) (tape 1) (tape 2)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) false
    (labels .tableOut) (labels .tableBack) (some (labels (.skip 0))) program
    (atLabels .tableOut) (atLabels .tableBack) (workTapes tape base [] output)
    scratch ambient none
  rw [source, workTapes_input tape distinct, List.append_nil, update_input tape distinct] at run
  exact run

theorem skipTrace (formula : Formula) (output : List Bool) :
    (advance (TM2.step program))^[formula.variables + 1]
      (some ⟨some (labels (.skip 0)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.bits formula) output⟩) =
      some ⟨some (labels .readCount), clean ambient,
        workTapes tape base (encodeWord formula.clauses.length ++
          SourceOccurrenceEncoding.body 0 formula.clauses) output⟩ := by
  have run := UnaryBlockSkipMachine.listTrace (tape 1) (fun slot => labels (.skip slot))
    (some (labels .readCount)) rejected program (fun slot => atLabels (.skip slot))
    (workTapes tape base [] output) ambient [formula.variables] rfl
    (encodeWord formula.clauses.length ++ SourceOccurrenceEncoding.body 0 formula.clauses) none
  have headerLength : (encodeWords [formula.variables]).length = formula.variables + 1 := by
    simp [encodeWords, encodeWord_length]
  have headerInput : encodeWords [formula.variables] ++
      (encodeWord formula.clauses.length ++ SourceOccurrenceEncoding.body 0 formula.clauses) =
        SourceOccurrenceEncoding.bits formula := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp [encodeWords, List.append_assoc]
  rw [headerLength, headerInput, update_input tape distinct, update_input tape distinct] at run
  exact run

theorem readTrace (m : Nat) (body output : List Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some (labels .readCount), clean ambient,
        workTapes tape base (encodeWord m ++ body) output⟩) =
      some ⟨some (labels .drain), clean ambient,
        workTapes tape base body (List.replicate m true ++ output)⟩ := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  exact Hastad.SourceMachine.fieldLoopTrace (tape 1) (tape 3) different
    (labels .readCount) (some (labels .drain)) program (atLabels .readCount)
    base m body output ambient none

theorem drainTrace (body output : List Bool) :
    (advance (TM2.step program))^[body.length + 1]
      (some ⟨some (labels .drain), clean ambient, workTapes tape base body output⟩) =
      some ⟨done, clean ambient, workTapes tape base [] output⟩ := by
  have run := MachineDrain.drainTrace (tape 1) (labels .drain) done program
    (atLabels .drain) (workTapes tape base [] output) body ambient none
  rw [update_input tape distinct, update_input tape distinct] at run
  exact run

theorem countTrace (formula : Formula)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (copyEmpty : base (tape 1) = []) (scratchEmpty : base (tape 2) = []) :
    (advance (TM2.step program))^[steps formula]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨done, clean ambient, Function.update base (tape 3)
        (List.replicate formula.clauses.length true ++ base (tape 3))⟩ := by
  have first := copyTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.bits formula) (base (tape 3)) tableWord scratchEmpty
  have second := skipTrace tape distinct labels done rejected program atLabels base ambient
    formula (base (tape 3))
  have third := readTrace tape distinct labels done rejected program atLabels base ambient
    formula.clauses.length (SourceOccurrenceEncoding.body 0 formula.clauses) (base (tape 3))
  have fourth := drainTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.body 0 formula.clauses)
    (List.replicate formula.clauses.length true ++ base (tape 3))
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have empty (output : List Bool) :
      workTapes tape base [] output = Function.update base (tape 3) output :=
    workTapes_empty tape base output copyEmpty
  simpa only [steps, main, empty, Function.update_eq_self] using full

def countInTime (formula : Formula)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (copyEmpty : base (tape 1) = []) (scratchEmpty : base (tape 2) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), clean ambient, base⟩
      (some ⟨done, clean ambient, Function.update base (tape 3)
        (List.replicate formula.clauses.length true ++ base (tape 3))⟩)
      (3 * ((SourceOccurrenceEncoding.bits formula).length + 1)) where
  steps := steps formula
  evals_in_steps := countTrace tape distinct labels done rejected program atLabels base ambient
    formula tableWord copyEmpty scratchEmpty
  steps_le_m := (steps_eq formula).le

omit [DecidableEq K] distinct atLabels in
theorem label_finite : Finite Label := inferInstance

end PerfectCompleteness.SourceClauseCountMachine

end OAI

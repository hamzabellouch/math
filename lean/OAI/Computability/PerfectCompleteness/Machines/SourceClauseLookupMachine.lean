import OAI.Computability.PerfectCompleteness.Machines.SourceClauseSelectMachine
import OAI.Computability.PerfectCompleteness.Machines.UnaryBlockSkipMachine
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain

namespace OAI


namespace PerfectCompleteness.SourceClauseLookupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean {A : Type} (ambient : A) : State A := (ambient, none)

inductive Label
  | tableOut | tableBack | indexOut | indexBack
  | header (slot : Fin 2)
  | select (label : SourceClauseSelectMachine.Label)
  | drain
  deriving DecidableEq, Fintype

def main : Label := .tableOut

def selectMap : Fin 3 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 5

theorem body_drop_length_le {n : Nat} (clauses : List (Clause n)) (first k : Nat) :
    (SourceOccurrenceEncoding.body (first + k) (clauses.drop k)).length ≤
      (SourceOccurrenceEncoding.body first clauses).length := by
  induction clauses generalizing first k with
  | nil => simp
  | cons clause clauses ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [List.drop_succ_cons, SourceOccurrenceEncoding.body_cons, List.length_append]
          have tail := ih (first + 1) k
          have indexEq : first + (k + 1) = first + 1 + k := by omega
          rw [indexEq]
          omega

def suffix (formula : Formula) (k : Nat) : List Bool :=
  SourceOccurrenceEncoding.body (k + 1) (formula.clauses.drop (k + 1))

def steps (formula : Formula) (k : Nat) : Nat :=
  2 * ((SourceOccurrenceEncoding.bits formula).length + 1) + 2 * (k + 1) +
    (formula.variables + formula.clauses.length + 2) +
    SourceClauseSelectMachine.steps 0 formula.clauses k + (suffix formula k).length + 1

theorem steps_le (formula : Formula) (k : Nat) (bound : k < formula.clauses.length) :
    steps formula k ≤ 10 * ((SourceOccurrenceEncoding.bits formula).length + k + 1) := by
  have tableLength : (SourceOccurrenceEncoding.bits formula).length =
      formula.variables + formula.clauses.length + 2 +
        (SourceOccurrenceEncoding.body 0 formula.clauses).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  have selectBound := SourceClauseSelectMachine.steps_le formula.clauses 0 k bound
  have suffixBound : (suffix formula k).length ≤
      (SourceOccurrenceEncoding.body 0 formula.clauses).length := by
    simpa only [suffix, Nat.zero_add] using body_drop_length_le formula.clauses 0 (k + 1)
  unfold steps
  omega

variable {K Λ A : Type} [DecidableEq K]

def selectTapes (tape : Fin 6 → K) : Fin 3 → K := fun i => tape (selectMap i)

omit [DecidableEq K] in
theorem selectTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (selectTapes tape) :=
  distinct.comp (by decide : Function.Injective selectMap)

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .tableOut => loopAt (tape 0) (tape 4) id false
      (labels .tableOut) (some (labels .tableBack))
  | .tableBack => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .tableBack) (some (labels .indexOut))
  | .indexOut => loopAt (tape 1) (tape 4) id false
      (labels .indexOut) (some (labels .indexBack))
  | .indexBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .indexBack) (some (labels (.header 0)))
  | .header slot => UnaryBlockSkipMachine.instruction (tape 2) (labels (.header slot))
      (UnaryBlockSkipMachine.nextField (fun slot => labels (.header slot))
        (some (labels (.select .guard))) slot) rejected
  | .select label => SourceClauseSelectMachine.instruction (selectTapes tape)
      (fun label => labels (.select label)) (some (labels .drain)) rejected label
  | .drain => MachineDrain.drain (tape 2) (labels .drain) done

def workTapes (tape : Fin 6 → K) (base : K → List Bool)
    (input counter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base (tape 2) input)
    (tape 3) counter) (tape 5) output

@[simp] theorem workTapes_output (tape : Fin 6 → K) (base : K → List Bool)
    (input counter output : List Bool) :
    workTapes tape base input counter output (tape 5) = output := by
  simp [workTapes]

theorem workTapes_input (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output : List Bool) :
    workTapes tape base input counter output (tape 2) = input := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [workTapes, hd]

theorem workTapes_counter (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output : List Bool) :
    workTapes tape base input counter output (tape 3) = counter := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [workTapes, hd]

private theorem update_input (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output replacement : List Bool) :
    Function.update (workTapes tape base input counter output) (tape 2) replacement =
      workTapes tape base replacement counter output := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [workTapes, hd]
  · simp [workTapes, h, Function.update_apply]

private theorem update_counter (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output replacement : List Bool) :
    Function.update (workTapes tape base input counter output) (tape 3) replacement =
      workTapes tape base input replacement output := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 3
  · subst k; simp [workTapes, hd]
  · simp [workTapes, h, Function.update_apply]

theorem workTapes_empty (tape : Fin 6 → K) (base : K → List Bool) (output : List Bool)
    (tableCopyEmpty : base (tape 2) = []) (indexCopyEmpty : base (tape 3) = []) :
    workTapes tape base [] [] output = Function.update base (tape 5) output := by
  have tableSelf := Function.update_eq_self (tape 2) base
  have indexSelf := Function.update_eq_self (tape 3) base
  rw [tableCopyEmpty] at tableSelf
  rw [indexCopyEmpty] at indexSelf
  simp only [workTapes, tableSelf, indexSelf]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem copyTableTrace (table output : List Bool)
    (tableWord : base (tape 0) = table) (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[2 * (table.length + 1)]
      (some ⟨some (labels .tableOut), clean ambient, workTapes tape base [] [] output⟩) =
      some ⟨some (labels .indexOut), clean ambient, workTapes tape base table [] output⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have source : workTapes tape base [] [] output (tape 0) = table := by
    simp [workTapes, hd, tableWord]
  have scratch : workTapes tape base [] [] output (tape 4) = [] := by
    simp [workTapes, hd, scratchEmpty]
  have run := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    (labels .tableOut) (labels .tableBack) (some (labels .indexOut)) program
    (atLabels .tableOut) (atLabels .tableBack) (workTapes tape base [] [] output)
    scratch ambient none
  rw [source, workTapes_input tape distinct, List.append_nil, update_input tape distinct] at run
  exact run

theorem copyIndexTrace (table output : List Bool) (k : Nat)
    (indexWord : base (tape 1) = List.replicate k true) (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[2 * (k + 1)]
      (some ⟨some (labels .indexOut), clean ambient, workTapes tape base table [] output⟩) =
      some ⟨some (labels (.header 0)), clean ambient,
        workTapes tape base table (List.replicate k true) output⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have source : workTapes tape base table [] output (tape 1) = List.replicate k true := by
    simp [workTapes, hd, indexWord]
  have scratch : workTapes tape base table [] output (tape 4) = [] := by
    simp [workTapes, hd, scratchEmpty]
  have run := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
    (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
    (labels .indexOut) (labels .indexBack) (some (labels (.header 0))) program
    (atLabels .indexOut) (atLabels .indexBack) (workTapes tape base table [] output)
    scratch ambient none
  rw [source, List.length_replicate, workTapes_counter tape distinct,
    List.append_nil, update_counter tape distinct] at run
  exact run

theorem headerTrace (formula : Formula) (k : Nat) (output : List Bool) :
    (advance (TM2.step program))^[formula.variables + formula.clauses.length + 2]
      (some ⟨some (labels (.header 0)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.bits formula) (List.replicate k true) output⟩) =
      some ⟨some (labels (.select .guard)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.body 0 formula.clauses)
          (List.replicate k true) output⟩ := by
  have run := UnaryBlockSkipMachine.listTrace (tape 2) (fun slot => labels (.header slot))
    (some (labels (.select .guard))) rejected program (fun slot => atLabels (.header slot))
    (workTapes tape base [] (List.replicate k true) output) ambient
    [formula.variables, formula.clauses.length] rfl
    (SourceOccurrenceEncoding.body 0 formula.clauses) none
  have headerLength : (encodeWords [formula.variables, formula.clauses.length]).length =
      formula.variables + formula.clauses.length + 2 := by
    simp [encodeWords_length]
  have headerInput : encodeWords [formula.variables, formula.clauses.length] ++
      SourceOccurrenceEncoding.body 0 formula.clauses = SourceOccurrenceEncoding.bits formula := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp [encodeWords, List.append_assoc]
  rw [headerLength, headerInput, update_input tape distinct, update_input tape distinct] at run
  exact run

theorem drainTrace (input output : List Bool) :
    (advance (TM2.step program))^[input.length + 1]
      (some ⟨some (labels .drain), clean ambient, workTapes tape base input [] output⟩) =
      some ⟨done, clean ambient, workTapes tape base [] [] output⟩ := by
  have run := MachineDrain.drainTrace (tape 2) (labels .drain) done program
    (atLabels .drain) (workTapes tape base [] [] output) input ambient none
  rw [update_input tape distinct, update_input tape distinct] at run
  exact run

theorem selectTrace (formula : Formula) (k : Nat) (bound : k < formula.clauses.length)
    (output : List Bool) :
    (advance (TM2.step program))^[SourceClauseSelectMachine.steps 0 formula.clauses k]
      (some ⟨some (labels (.select .guard)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.body 0 formula.clauses)
          (List.replicate k true) output⟩) =
      some ⟨some (labels .drain), clean ambient,
        workTapes tape base (suffix formula k) []
          ((encodeWords (clauseWords formula.clauses[k])).reverse ++ output)⟩ := by
  have updated (input : List Bool) (index : Nat) (out : List Bool) :
      SourceClauseSelectMachine.selectTapes (selectTapes tape) base input index out =
        workTapes tape base input (List.replicate index true) out := rfl
  have run := SourceClauseSelectMachine.selectTrace (selectTapes tape)
    (selectTapes_injective tape distinct) (fun label => labels (.select label))
    (some (labels .drain)) rejected program (fun label => atLabels (.select label))
    base ambient formula.clauses 0 k bound [] output
  simp only [updated, List.append_nil, List.replicate_zero, Nat.zero_add] at run
  exact run

theorem lookupTrace (formula : Formula) (k : Nat) (bound : k < formula.clauses.length)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate k true)
    (tableCopyEmpty : base (tape 2) = []) (indexCopyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps formula k]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨done, clean ambient, Function.update base (tape 5)
        ((encodeWords (clauseWords formula.clauses[k])).reverse ++ base (tape 5))⟩ := by
  have first := copyTableTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.bits formula) (base (tape 5)) tableWord scratchEmpty
  have second := copyIndexTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.bits formula) (base (tape 5)) k indexWord scratchEmpty
  have third := headerTrace tape distinct labels done rejected program atLabels base ambient
    formula k (base (tape 5))
  have fourth := selectTrace tape distinct labels done rejected program atLabels base ambient
    formula k bound (base (tape 5))
  have fifth := drainTrace tape distinct labels done rejected program atLabels base ambient
    (suffix formula k) ((encodeWords (clauseWords formula.clauses[k])).reverse ++ base (tape 5))
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth
  have count :
      ((2 * ((SourceOccurrenceEncoding.bits formula).length + 1) + 2 * (k + 1) +
          (formula.variables + formula.clauses.length + 2)) +
        SourceClauseSelectMachine.steps 0 formula.clauses k) +
          ((suffix formula k).length + 1) = steps formula k := by
    unfold steps
    omega
  have empty (output : List Bool) :
      workTapes tape base [] [] output = Function.update base (tape 5) output :=
    workTapes_empty tape base output tableCopyEmpty indexCopyEmpty
  simpa only [count, main, empty, Function.update_eq_self] using full

def lookupInTime (formula : Formula) (k : Nat) (bound : k < formula.clauses.length)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate k true)
    (tableCopyEmpty : base (tape 2) = []) (indexCopyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), clean ambient, base⟩
      (some ⟨done, clean ambient, Function.update base (tape 5)
        ((encodeWords (clauseWords formula.clauses[k])).reverse ++ base (tape 5))⟩)
      (10 * ((SourceOccurrenceEncoding.bits formula).length + k + 1)) where
  steps := steps formula k
  evals_in_steps := lookupTrace tape distinct labels done rejected program atLabels base ambient
    formula k bound tableWord indexWord tableCopyEmpty indexCopyEmpty scratchEmpty
  steps_le_m := steps_le formula k bound

omit [DecidableEq K] distinct atLabels in
theorem label_finite : Finite Label := inferInstance

end PerfectCompleteness.SourceClauseLookupMachine

end OAI

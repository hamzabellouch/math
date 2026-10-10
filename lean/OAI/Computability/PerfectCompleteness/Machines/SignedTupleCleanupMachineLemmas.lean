import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.PerfectCompleteness.Foundations.SignedTupleLayout
import OAI.Computability.PerfectCompleteness.Machines.SourceTupleMachine
import OAI.Computability.PerfectCompleteness.Reduction.CompletionLemmas
import OAI.Computability.PerfectCompleteness.Reduction.SignedCompletionSchedule
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteTable

namespace OAI


namespace PerfectCompleteness.SignedTupleCleanupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra
abbrev State (width : Nat) (U Desc : Type) := SignedTupleLayout.State width U Desc
abbrev Alphabet {width : Nat} {Extra : Type} (_ : Tape width Extra) := Bool

variable {width : Nat} {Extra U Desc Λ : Type}

def localTapes (position : Fin width) : List (Tape width Extra) :=
  [.source (.digit position),
   .source (.variableName position 0), .source (.variableName position 1),
   .source (.variableName position 2),
   .encodedVariable position 0, .encodedVariable position 1, .encodedVariable position 2]

def chosen (width : Nat) (Extra : Type) : List (Tape width Extra) :=
  (List.finRange width).flatMap localTapes

def selected : Tape width Extra → Bool
  | .source (.digit _) => true
  | .source (.variableName _ _) => true
  | .encodedVariable _ _ => true
  | _ => false

@[simp] theorem chosen_length (width : Nat) (Extra : Type) :
    (chosen width Extra).length = 7 * width := by
  have lengthFor (positions : List (Fin width)) :
      (positions.flatMap (localTapes (Extra := Extra))).length = 7 * positions.length := by
    induction positions with
    | nil => rfl
    | cons position positions ih =>
        simp only [List.flatMap_cons, List.length_append, localTapes, List.length_cons,
          List.length_nil, ih]
        omega
  simpa only [chosen, List.length_finRange] using lengthFor (List.finRange width)

@[simp] theorem mem_chosen (tape : Tape width Extra) :
    tape ∈ chosen width Extra ↔ selected tape = true := by
  cases tape with
  | source source =>
      cases source with
      | table => simp [chosen, localTapes, selected]
      | digit position => simp [chosen, localTapes, selected]
      | work slot => simp [chosen, localTapes, selected]
      | variableName position slot =>
          fin_cases slot <;> simp [chosen, localTapes, selected]
  | encodedVariable position slot =>
      fin_cases slot <;> simp [chosen, localTapes, selected]
  | current position => simp [chosen, localTapes, selected]
  | remaining position => simp [chosen, localTapes, selected]
  | adapterScratch => simp [chosen, localTapes, selected]
  | edgeWork slot => simp [chosen, localTapes, selected]
  | edgeCount => simp [chosen, localTapes, selected]
  | extra value => simp [chosen, localTapes, selected]

theorem finalTapes_eq (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (clear : SignedTupleLayout.Clear base) :
    MachineDrainMany.finalTapes (chosen width Extra)
      (SignedTupleLayout.preparedTapes formula indices base) = base := by
  funext tape
  simp only [MachineDrainMany.finalTapes_apply, mem_chosen]
  cases tape with
  | source source =>
      cases source with
      | table => simp [selected, SignedTupleLayout.preparedTapes]
      | digit position => simp [selected, clear.rawDigits]
      | work slot => simp [selected, SignedTupleLayout.preparedTapes]
      | variableName position slot => simp [selected, clear.rawVariables]
  | encodedVariable position slot => simp [selected, clear.encodedVariables]
  | current position => simp [selected, SignedTupleLayout.preparedTapes]
  | remaining position => simp [selected, SignedTupleLayout.preparedTapes]
  | adapterScratch => simp [selected, SignedTupleLayout.preparedTapes]
  | edgeWork slot => simp [selected, SignedTupleLayout.preparedTapes]
  | edgeCount => simp [selected, SignedTupleLayout.preparedTapes]
  | extra value => simp [selected, SignedTupleLayout.preparedTapes]

theorem selected_length_le (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (tape : Tape width Extra) (h : selected tape = true) :
    (SignedTupleLayout.preparedTapes formula indices base tape).length ≤
      (SourceOccurrenceEncoding.bits formula).length + 1 := by
  cases tape with
  | source source =>
      cases source with
      | table => simp [selected] at h
      | digit position =>
          have bounded := (indices position).isLt
          have tableBound := SourceTupleResetMachine.clause_count_le_table formula
          simp only [SignedTupleLayout.preparedTapes, List.length_replicate]
          omega
      | work slot => simp [selected] at h
      | variableName position slot =>
          have bounded :=
            (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
          have tableBound := SourceTupleResetMachine.variable_count_le_table formula
          simp only [SignedTupleLayout.preparedTapes, List.length_replicate,
            SignedTupleLayout.vars]
          omega
  | encodedVariable position slot =>
      have bounded :=
        (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
      have tableBound := SourceTupleResetMachine.variable_count_le_table formula
      simp only [SignedTupleLayout.preparedTapes, encodeWord_length, SignedTupleLayout.vars]
      omega
  | current position => simp [selected] at h
  | remaining position => simp [selected] at h
  | adapterScratch => simp [selected] at h
  | edgeWork slot => simp [selected] at h
  | edgeCount => simp [selected] at h
  | extra value => simp [selected] at h

def steps (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Nat :=
  MachineDrainMany.steps (chosen width Extra) (SignedTupleLayout.preparedTapes formula indices base)

theorem steps_le (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) :
    steps formula indices base ≤
      7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) := by
  let tapes := SignedTupleLayout.preparedTapes formula indices base
  let bound := (SourceOccurrenceEncoding.bits formula).length + 1
  have sumBound : ∀ keys : List (Tape width Extra),
      (∀ tape ∈ keys, (tapes tape).length ≤ bound) →
      MachineDrainMany.lengthSum keys tapes ≤ keys.length * bound := by
    intro keys
    induction keys with
    | nil => intro _; simp [MachineDrainMany.lengthSum]
    | cons tape keys ih =>
        intro bounded
        have first := bounded tape (by simp)
        have rest := ih (fun other member => bounded other (List.mem_cons_of_mem tape member))
        simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
          List.length_cons, Nat.add_mul, Nat.one_mul] at rest ⊢
        omega
  have bounded := sumBound (chosen width Extra) (fun tape member =>
    selected_length_le formula indices base tape ((mem_chosen tape).mp member))
  have drains := MachineDrainMany.steps_le (chosen width Extra) tapes
  rw [chosen_length] at bounded drains
  change MachineDrainMany.steps (chosen width Extra) tapes ≤ _
  dsimp only [bound] at bounded
  calc
    MachineDrainMany.steps (chosen width Extra) tapes ≤
        7 * width * ((SourceOccurrenceEncoding.bits formula).length + 1) + 7 * width := by omega
    _ = 7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega

abbrev Label (width : Nat) (Extra : Type) := MachineDrainMany.Label (chosen width Extra)

def instruction (labels : Label width Extra → Λ) (exit : Option Λ) :
    Label width Extra → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc) :=
  MachineDrainMany.instruction (chosen width Extra) labels exit

def entry (labels : Label width Extra → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry (chosen width Extra) labels exit

theorem cleanupTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U)
    (labels : Label width Extra → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc))
    (atLabels : ∀ label, program (labels label) =
      instruction (width := width) (Extra := Extra) labels exit label) :
    (advance (TM2.step program))^[steps formula indices base]
      (some ⟨entry (width := width) (Extra := Extra) labels exit,
        SignedTupleLayout.preparedState formula indices ambient,
        SignedTupleLayout.preparedTapes formula indices base⟩) =
      some ⟨exit, SignedTupleLayout.preparedState formula indices ambient, base⟩ := by
  have run := MachineDrainMany.trace (chosen width Extra) labels exit program atLabels
    (SignedTupleLayout.preparedTapes formula indices base)
    (SignedTupleLayout.preparedState (Desc := Desc) formula indices ambient).1 none
  rw [MachineDrainMany.finalRegister_none, finalTapes_eq formula indices base input.toClear] at run
  exact run

def cleanupInTime (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U)
    (labels : Label width Extra → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc))
    (atLabels : ∀ label, program (labels label) =
      instruction (width := width) (Extra := Extra) labels exit label) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry (width := width) (Extra := Extra) labels exit,
        SignedTupleLayout.preparedState formula indices ambient,
        SignedTupleLayout.preparedTapes formula indices base⟩
      (some ⟨exit, SignedTupleLayout.preparedState formula indices ambient, base⟩)
      (7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2)) where
  steps := steps formula indices base
  evals_in_steps := cleanupTrace formula indices base input ambient labels exit program atLabels
  steps_le_m := steps_le formula indices base

theorem finiteLabels : Finite (Label width Extra) := inferInstance

end
end PerfectCompleteness.SignedTupleCleanupMachine


namespace PerfectCompleteness.SignedTuplePreparationMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding
open SignedTupleLayout
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra
abbrev State (width : Nat) (U Desc : Type) := SignedTupleLayout.State width U Desc
abbrev Alphabet {width : Nat} {Extra : Type} (_ : Tape width Extra) := Bool

variable {width : Nat} {Extra U Desc Λ : Type}

def variableEquiv (width : Nat) : Fin (width * 3) ≃ Fin width × Fin 3 := finProdFinEquiv.symm

def digitTape : FixedUnaryRepresentationPlacement.Tape width → Tape width Extra
  | .source i => .current i
  | .destination i => .source (.digit i)
  | .scratch => .adapterScratch

def digitView : Tape width Extra → Option (FixedUnaryRepresentationPlacement.Tape width)
  | .current i => some (.source i)
  | .source (.digit i) => some (.destination i)
  | .adapterScratch => some .scratch
  | _ => none

theorem digitView_left (k : FixedUnaryRepresentationPlacement.Tape width) :
    digitView (digitTape (Extra := Extra) k) = some k := by
  cases k <;> rfl

theorem digitView_right (j : Tape width Extra) (k : FixedUnaryRepresentationPlacement.Tape width)
    (h : digitView j = some k) : digitTape k = j := by
  cases j with
  | source localTape =>
      cases localTape <;> simp_all [digitView, digitTape]
      subst k
      rfl
  | current i =>
      simp only [digitView, Option.some.injEq] at h
      subst k
      rfl
  | remaining i => simp_all [digitView]
  | encodedVariable i s => simp_all [digitView]
  | adapterScratch =>
      simp only [digitView, Option.some.injEq] at h
      subst k
      rfl
  | edgeWork s => simp_all [digitView]
  | edgeCount => simp_all [digitView]
  | extra v => simp_all [digitView]

def variableTape : FixedUnaryRepresentationPlacement.Tape (width * 3) → Tape width Extra
  | .source i => .source (.variableName ((variableEquiv width) i).1 ((variableEquiv width) i).2)
  | .destination i => .encodedVariable ((variableEquiv width) i).1 ((variableEquiv width) i).2
  | .scratch => .adapterScratch

def variableView : Tape width Extra → Option (FixedUnaryRepresentationPlacement.Tape (width * 3))
  | .source (.variableName i s) => some (.source ((variableEquiv width).symm (i, s)))
  | .encodedVariable i s => some (.destination ((variableEquiv width).symm (i, s)))
  | .adapterScratch => some .scratch
  | _ => none

theorem variableView_left (k : FixedUnaryRepresentationPlacement.Tape (width * 3)) :
    variableView (variableTape (Extra := Extra) k) = some k := by
  cases k <;> simp [variableView, variableTape]

theorem variableView_right (j : Tape width Extra)
    (k : FixedUnaryRepresentationPlacement.Tape (width * 3))
    (h : variableView j = some k) : variableTape k = j := by
  cases j with
  | source localTape =>
      cases localTape <;> simp_all [variableView, variableTape]
      subst k
      simp
  | current i => simp_all [variableView]
  | remaining i => simp_all [variableView]
  | encodedVariable i s =>
      simp only [variableView, Option.some.injEq] at h
      subst k
      simp [variableTape]
  | adapterScratch =>
      simp only [variableView, Option.some.injEq] at h
      subst k
      rfl
  | edgeWork s => simp_all [variableView]
  | edgeCount => simp_all [variableView]
  | extra v => simp_all [variableView]

def variableValues (formula : Formula) (indices : Fin width → Fin formula.clauses.length) :
    Fin (width * 3) → Nat :=
  fun i => vars formula indices ((variableEquiv width) i).1 ((variableEquiv width) i).2

inductive Label (width : Nat)
  | digits (label : FixedUnaryRepresentationPlacement.Label .encodedToRaw width)
  | extract (label : SourceTupleBodyPlacement.Label width)
  | variableCopies (label : FixedUnaryRepresentationPlacement.Label .rawToEncoded (width * 3))
  deriving DecidableEq, Fintype

def variableEntry (labels : Label width → Λ) (exit : Option Λ) : Option Λ :=
  FixedUnaryRepresentationPlacement.entry .rawToEncoded (fun l => labels (.variableCopies l)) exit

def sourceEntry (labels : Label width → Λ) (exit : Option Λ) : Option Λ :=
  SourceTuplePlacement.entry (fun l => labels (.extract l)) (variableEntry labels exit)

def entry (labels : Label width → Λ) (exit : Option Λ) : Option Λ :=
  FixedUnaryRepresentationPlacement.entry .encodedToRaw (fun l => labels (.digits l))
    (sourceEntry labels exit)

def instruction (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ (State width U Desc)
  | .digits label => FixedUnaryRepresentationPlacement.instruction .encodedToRaw digitTape
      (fun l => labels (.digits l)) (sourceEntry labels exit) label
  | .extract label => SourceTupleBodyPlacement.instruction SignedTupleLayout.Tape.source
      (fun l => labels (.extract l)) (variableEntry labels exit) label
  | .variableCopies label => FixedUnaryRepresentationPlacement.instruction .rawToEncoded variableTape
      (fun l => labels (.variableCopies l)) exit label

theorem digit_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes digitView base .encodedToRaw
      (ids formula indices) (fun _ => []) = base := by
  apply FixedUnaryRepresentationPlacement.tapes_eq_base digitTape digitView digitView_right
  intro k
  cases k with
  | source i => exact input.current i
  | destination i => exact input.rawDigits i
  | scratch => exact input.scratch

theorem digit_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes digitView base .encodedToRaw
      (ids formula indices)
      (fun i => FixedUnaryRepresentationMachine.targetWord .encodedToRaw (ids formula indices i) ++ []) =
      digitTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [FixedUnaryRepresentationPlacement.tapes,
      Placement.tapes, digitView, FixedUnaryRepresentationMachine.stacks,
      FixedUnaryRepresentationMachine.targetWord, digitTapes, ids]
  | current i => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes, digitView,
      FixedUnaryRepresentationMachine.stacks, FixedUnaryRepresentationMachine.sourceWord,
      digitTapes, ids, input.current]
  | remaining i => rfl
  | encodedVariable i s => rfl
  | adapterScratch => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes, digitView,
      FixedUnaryRepresentationMachine.stacks, digitTapes, input.scratch]
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

theorem source_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    SourceTuplePlacement.tapes sourceView (digitTapes formula indices base)
      formula indices (fun _ => false) = digitTapes formula indices base := by
  apply SourceTuplePlacement.tapes_eq_base SignedTupleLayout.Tape.source sourceView sourceView_right
  intro k
  cases k with
  | table => exact input.table
  | digit i => rfl
  | work s => exact input.sourceWork s
  | variableName i s => exact input.rawVariables i s

theorem source_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    SourceTuplePlacement.tapes sourceView (digitTapes formula indices base)
      formula indices (fun _ => true) = rawTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [SourceTuplePlacement.tapes, Placement.tapes,
      sourceView, SourceTupleData.stacks, NormalizationReadMachine.clauseCounters,
      rawTapes, vars, input.table, input.sourceWork]
  | current i => rfl
  | remaining i => rfl
  | encodedVariable i s => rfl
  | adapterScratch => rfl
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

theorem variable_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes variableView (rawTapes formula indices base) .rawToEncoded
      (variableValues formula indices) (fun _ => []) = rawTapes formula indices base := by
  apply FixedUnaryRepresentationPlacement.tapes_eq_base variableTape variableView variableView_right
  intro k
  cases k <;> simp [variableTape, FixedUnaryRepresentationMachine.stacks,
    FixedUnaryRepresentationMachine.sourceWord, rawTapes, variableValues,
    input.encodedVariables, input.scratch]

theorem variable_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes variableView (rawTapes formula indices base) .rawToEncoded
      (variableValues formula indices)
      (fun i => FixedUnaryRepresentationMachine.targetWord .rawToEncoded
        (variableValues formula indices i) ++ []) = preparedTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [FixedUnaryRepresentationPlacement.tapes,
      Placement.tapes, variableView, FixedUnaryRepresentationMachine.stacks,
      FixedUnaryRepresentationMachine.sourceWord, variableValues, rawTapes, preparedTapes]
  | current i => rfl
  | remaining i => rfl
  | encodedVariable i s => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes,
      variableView, FixedUnaryRepresentationMachine.stacks, FixedUnaryRepresentationMachine.targetWord,
      variableValues, preparedTapes]
  | adapterScratch => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes,
      variableView, FixedUnaryRepresentationMachine.stacks, preparedTapes, input.scratch]
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

def budget (width tableLength : Nat) : Nat :=
  width * (2 * tableLength + 3) + width * (60 * (tableLength + 1)) +
    (width * 3) * (2 * tableLength + 3)

theorem budget_le (width tableLength : Nat) :
    budget width tableLength ≤ 72 * width * (tableLength + 1) := by
  unfold budget
  nlinarith [Nat.zero_le (width * tableLength)]

variable [DecidableEq Extra]

def prepareInTime (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) (ambient : U)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ (State width U Desc))
    (atLabels : ∀ l, program (labels l) = instruction labels exit l) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit, clean ambient, base⟩
      (some ⟨exit, preparedState formula indices ambient, preparedTapes formula indices base⟩)
      (budget width (SourceOccurrenceEncoding.bits formula).length) := by
  have idsBound (i : Fin width) : ids formula indices i ≤ (SourceOccurrenceEncoding.bits formula).length :=
    Nat.le_trans (Nat.le_of_lt (indices i).isLt) (SourceTupleResetMachine.clause_count_le_table formula)
  have varsBound (i : Fin (width * 3)) :
      variableValues formula indices i ≤ (SourceOccurrenceEncoding.bits formula).length := by
    let position := ((variableEquiv width) i).1
    let slot := ((variableEquiv width) i).2
    have bounded := (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
    exact Nat.le_trans (Nat.le_of_lt bounded)
      (SourceTupleResetMachine.variable_count_le_table formula)
  have digitsRun := FixedUnaryRepresentationPlacement.familyInTime .encodedToRaw
    (digitTape (Extra := Extra)) digitView digitView_left digitView_right
    (fun l => labels (.digits l)) (sourceEntry labels exit) program (fun l => atLabels (.digits l))
    base (ids formula indices) (fun _ => []) (clean (Desc := Desc) ambient).1
    (SourceOccurrenceEncoding.bits formula).length idsBound
  rw [digit_initial_eq formula indices base input, digit_final_eq formula indices base input] at digitsRun
  have sourceRun := SourceTupleBodyPlacement.tupleInTime (SignedTupleLayout.Tape.source (Extra := Extra)) sourceView
    sourceView_left sourceView_right (fun l => labels (.extract l)) (variableEntry labels exit)
    program (fun l => atLabels (.extract l)) (digitTapes formula indices base) formula indices ambient
    (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false) (frame Desc)
  rw [source_initial_eq formula indices base input, source_final_eq formula indices base input] at sourceRun
  have variablesRun := FixedUnaryRepresentationPlacement.familyInTime .rawToEncoded
    (variableTape (Extra := Extra)) variableView variableView_left variableView_right
    (fun l => labels (.variableCopies l)) exit program (fun l => atLabels (.variableCopies l))
    (rawTapes formula indices base) (variableValues formula indices) (fun _ => [])
    (preparedState (Desc := Desc) formula indices ambient).1
    (SourceOccurrenceEncoding.bits formula).length varsBound
  rw [variable_initial_eq formula indices base input, variable_final_eq formula indices base input] at variablesRun
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ digitsRun sourceRun) variablesRun
  have cleanEta : ((clean (width := width) (Desc := Desc) ambient).1, (none : Option Bool)) =
      clean (width := width) (Desc := Desc) ambient := rfl
  have preparedEta : ((preparedState (Desc := Desc) formula indices ambient).1, (none : Option Bool)) =
      preparedState (Desc := Desc) formula indices ambient := rfl
  simpa only [entry, sourceEntry, variableEntry, cleanEta, preparedEta,
    budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem finiteLabels : Finite (Label width) := inferInstance

end
end PerfectCompleteness.SignedTuplePreparationMachine


namespace PerfectCompleteness.SourceTupleScheduleMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MetadataFreeSampler
open scoped Classical

noncomputable section

def shapeSigns : CanonicalKeyShape.Shape → SourceClause.Triple
  | .clause signs => signs
  | .bit => (false, false, false)

def signTuple {branch : Nat → Nat} {n t : Nat}
    (shapes : Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape) :
    SignTuple branch n t :=
  fun leaf slot => shapeSigns (shapes (TreeCanonical.numbering branch n t (leaf, slot)))

def sourceSigns {branch : Nat → Nat} {n t : Nat} (formula : Formula)
    (indices : Fin (TreeCanonical.locationCount branch n t) → Fin formula.clauses.length) :
    SignTuple branch n t :=
  fun leaf slot =>
    let clause := SourceTupleData.selectedClause formula indices
      (TreeCanonical.numbering branch n t (leaf, slot))
    (clause[0].positive, clause[1].positive, clause[2].positive)

theorem signTuple_source {branch : Nat → Nat} {n t : Nat} (formula : Formula)
    (indices : Fin (TreeCanonical.locationCount branch n t) → Fin formula.clauses.length) :
    signTuple (fun position => SourceClauseReaderMachine.clauseShape
      (SourceTupleData.selectedClause formula indices position)) = sourceSigns formula indices := by
  rfl

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))

abbrev State (branch : Nat → Nat) (n t : Nat) (A : Type) :=
  SourceTupleMachine.State (TreeCanonical.locationCount branch n t) A

def table {A : Type} (control : State branch n t A) : List Bool :=
  SignedCompletionSchedule.outputBits (repeats := repeats) hq large hn hbranch hrows
    (signTuple control.1.1.2)

def keys {A : Type} [Fintype A] : List (State branch n t A) := Finset.univ.toList

theorem mem_keys {A : Type} [Fintype A] (control : State branch n t A) :
    control ∈ keys (branch := branch) (n := n) (t := t) := by
  simp [keys]

variable {K Λ A : Type} [DecidableEq K] [Fintype A]

abbrev Alphabet (_ : K) := Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State branch n t A) :=
  match exit with
  | none => .halt
  | some label => .goto (fun _ => label)

def instruction (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State branch n t A) :=
  MachineFiniteTable.emit destination (table (repeats := repeats) hq large hn hbranch hrows)
    keys (exitAt exit)

def pushBound (destination : K) : Nat :=
  MachineFiniteTable.tableBound (Γ := Alphabet (K := K)) destination
    (table (A := A) (repeats := repeats) hq large hn hbranch hrows) keys

omit [DecidableEq K] in
theorem instruction_pushBound (destination : K) (exit : Option Λ) :
    Runtime.statementPushBound (instruction (A := A) (repeats := repeats) hq large hn hbranch hrows destination exit) ≤
      pushBound (A := A) (repeats := repeats) hq large hn hbranch hrows destination := by
  have bound := MachineFiniteTable.emit_push_bound destination
    (table (A := A) (repeats := repeats) hq large hn hbranch hrows) keys (exitAt exit)
  cases exit <;> simpa only [instruction, pushBound, exitAt,
    Runtime.statementPushBound, Nat.add_zero] using bound

theorem scheduleStep (destination : K) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State branch n t A)) (label : Λ)
    (atLabel : program label = instruction (repeats := repeats) hq large hn hbranch hrows destination exit)
    (control : State branch n t A) (base : K → List Bool) :
    TM2.step program ⟨some label, control, base⟩ =
      some ⟨exit, control, Function.update base destination
        (table (repeats := repeats) hq large hn hbranch hrows control ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) control base) = _
  rw [atLabel]
  unfold instruction
  rw [MachineFiniteTable.stepAux_emit (Γ := fun _ : K => Bool)
    (Λ := Λ) (σ := State branch n t A) destination
    (table (A := A) (repeats := repeats) hq large hn hbranch hrows)
    (keys (branch := branch) (n := n) (t := t) (A := A))
    (mem_keys (branch := branch) (n := n) (t := t) (A := A))
    (exitAt (K := K) (branch := branch) (n := n) (t := t) (A := A) exit)
    control base]
  cases exit <;> rfl

theorem sourceTrace (destination : K) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State branch n t A)) (label : Λ)
    (atLabel : program label = instruction (repeats := repeats) hq large hn hbranch hrows destination exit)
    (formula : Formula)
    (indices : Fin (TreeCanonical.locationCount branch n t) → Fin formula.clauses.length)
    (ambient : A) (signs : NormalizationReadMachine.Signs) (base : K → List Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some label, SourceClauseReaderMachine.clean
        (ambient, fun position => SourceClauseReaderMachine.clauseShape
          (SourceTupleData.selectedClause formula indices position)) signs, base⟩) =
      some ⟨exit, SourceClauseReaderMachine.clean
        (ambient, fun position => SourceClauseReaderMachine.clauseShape
          (SourceTupleData.selectedClause formula indices position)) signs,
        Function.update base destination
          (SignedCompletionSchedule.outputBits (repeats := repeats) hq large hn hbranch hrows
            (sourceSigns formula indices) ++ base destination)⟩ := by
  simpa only [Function.iterate_one, advance_some, table,
    SourceClauseReaderMachine.clean, NormalizationReadMachine.clean, signTuple_source]
    using scheduleStep (repeats := repeats) hq large hn hbranch hrows destination exit program label atLabel
      (SourceClauseReaderMachine.clean
        (ambient, fun position => SourceClauseReaderMachine.clauseShape
          (SourceTupleData.selectedClause formula indices position)) signs) base

def sourceInTime (destination : K) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State branch n t A)) (label : Λ)
    (atLabel : program label = instruction (repeats := repeats) hq large hn hbranch hrows destination exit)
    (formula : Formula)
    (indices : Fin (TreeCanonical.locationCount branch n t) → Fin formula.clauses.length)
    (ambient : A) (signs : NormalizationReadMachine.Signs) (base : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, SourceClauseReaderMachine.clean
        (ambient, fun position => SourceClauseReaderMachine.clauseShape
          (SourceTupleData.selectedClause formula indices position)) signs, base⟩
      (some ⟨exit, SourceClauseReaderMachine.clean
        (ambient, fun position => SourceClauseReaderMachine.clauseShape
          (SourceTupleData.selectedClause formula indices position)) signs,
        Function.update base destination
          (SignedCompletionSchedule.outputBits (repeats := repeats) hq large hn hbranch hrows
            (sourceSigns formula indices) ++ base destination)⟩) 1 where
  steps := 1
  evals_in_steps := sourceTrace (repeats := repeats) hq large hn hbranch hrows destination exit program label atLabel
    formula indices ambient signs base
  steps_le_m := Nat.le_refl _

end
end PerfectCompleteness.SourceTupleScheduleMachine

end OAI

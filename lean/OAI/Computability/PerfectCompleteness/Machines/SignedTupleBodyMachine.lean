import OAI.Computability.PerfectCompleteness.Foundations.SignedTupleLayout
import OAI.Computability.PerfectCompleteness.Machines.SignedDescriptorStageMachine
import OAI.Computability.PerfectCompleteness.Machines.SignedTupleCleanupMachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas

namespace OAI


namespace PerfectCompleteness.SignedTupleBodyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) (Extra : Type) := SignedTupleLayout.Tape width Extra

inductive BodyLabel (locations steps : Nat) (Descriptor Extra : Type) where
  | start
  | prepare (label : SignedTuplePreparationMachine.Label locations)
  | edges (label : MachineFiniteSequence.Label
      (fun _ : Fin steps => SignedDescriptorStageMachine.Label Descriptor locations) (List.ofFn id))
  | cleanup (label : SignedTupleCleanupMachine.Label locations Extra)
  | reset
  deriving DecidableEq, Fintype

structure Data (width : Nat) where
  leftKeys : List (Key width)
  rightKeys : List (Key width)
  reversedOutput : List Bool
  count : Nat

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "width" => TreeCanonical.locationCount branch n t
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "Desc" => SignedDescriptorStageMachine.Descriptor
  (rows := rows) (repeats := repeats) hq large

variable {K Λ A : Type} [DecidableEq K]

def tapes (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (data : Data width) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (work 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens data.leftKeys)))
        (work 8) (BinaryNameSearch.stream (CanonicalVertexNames.tokens data.rightKeys)))
      (work 7) data.reversedOutput)
    countTape (encodeWord data.count)

def next (descriptor : Desc) (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (data : Data width) : Data width where
  leftKeys := data.leftKeys ++ [CompletedEdgeMachine.key hq large descriptor .left ids vars]
  rightKeys := data.rightKeys ++ [CompletedEdgeMachine.key hq large descriptor .right ids vars]
  reversedOutput :=
    (CompletedEdgeMachine.edgeBits hq large descriptor data.leftKeys data.rightKeys ids vars).reverse ++
      data.reversedOutput
  count := data.count + 1

theorem finalTapes_eq (descriptor : Desc) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (work : Fin 10 → K)
    (distinct : Function.Injective work) (countTape : K)
    (countAvoid : ∀ j, countTape ≠ work j) (base : K → List Bool) (data : Data width) :
    SignedDescriptorStageMachine.finalTapes hq large descriptor work countTape
        (tapes work countTape base data) data.leftKeys data.rightKeys ids vars =
      tapes work countTape base (next hq large descriptor ids vars data) := by
  have hd (i j : Fin 10) (hne : i ≠ j) : work i ≠ work j :=
    fun h => hne (distinct h)
  funext k
  by_cases hc : k = countTape
  · subst k
    simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
      tapes, next, countAvoid, encodeWord, List.replicate_succ]
  · by_cases hl : k = work 1
    · subst k
      simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
        tapes, next, hc, hd 1 8 (by decide), hd 1 7 (by decide)]
    · by_cases hr : k = work 8
      · subst k
        simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
          tapes, next, hc, hd 8 7 (by decide)]
      · by_cases ho : k = work 7
        · subst k
          simp [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
            tapes, next, hc]
        · simp only [SignedDescriptorStageMachine.finalTapes, CompletedEdgeMachine.finalTapes,
            tapes, Function.update_of_ne hc, Function.update_of_ne hl,
            Function.update_of_ne hr, Function.update_of_ne ho]

theorem tapes_frame (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (data : Data width) (k : K) (hc : k ≠ countTape)
    (hl : k ≠ work 1) (hr : k ≠ work 8) (ho : k ≠ work 7) :
    tapes work countTape base data k = base k := by
  simp only [tapes, Function.update_of_ne hc, Function.update_of_ne hl,
    Function.update_of_ne hr, Function.update_of_ne ho]

variable [Fintype A] [DecidableEq A]

abbrev StageLabel := SignedDescriptorStageMachine.Label Desc width
abbrev LocalLabel (_ : Fin D) := StageLabel (rows := rows) (repeats := repeats) hq large
abbrev Label (indices : List (Fin D)) :=
  MachineFiniteSequence.Label (LocalLabel (repeats := repeats) hq large hn hbranch hrows) indices
abbrev State := SignedDescriptorStageMachine.State (rows := rows) (repeats := repeats) hq large A

abbrev BodyState (U : Type) :=
  SignedDescriptorStageMachine.State (rows := rows) (repeats := repeats) hq large
    (SourceTupleMachine.State width U)

def localMain (_ : Fin D) : StageLabel (rows := rows) (repeats := repeats) hq large := .load

def localInstruction (selectSigns : A → SignTuple branch n t)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (countTape : K)
    (rejected : Option Λ) (i : Fin D)
    (labels : StageLabel (rows := rows) (repeats := repeats) hq large → Λ) (exit : Option Λ) :
    StageLabel (rows := rows) (repeats := repeats) hq large →
      TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large) :=
  SignedDescriptorStageMachine.instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
    source work countTape labels exit rejected

def instruction (selectSigns : A → SignTuple branch n t)
    (source : Fin width → Fin 6 → K) (work : Fin 10 → K) (countTape : K)
    (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit rejected : Option Λ) :
    Label (repeats := repeats) hq large hn hbranch hrows indices →
      TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large) :=
  MachineFiniteSequence.instruction _ (localMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows)
    (localInstruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns source work countTape rejected)
    indices labels exit

def entry (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry _ (localMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows) indices labels exit

def result (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) : List (Fin D) → Data width → Data width
  | [], data => data
  | i :: indices, data => result signs ids vars indices
      (next hq large (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i) ids vars data)

def budget (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (source : Fin width → Fin 6 → K)
    (work : Fin 10 → K) (countTape : K) (base : K → List Bool) :
    List (Fin D) → Data width → Nat
  | [], _ => 0
  | i :: indices, data =>
      let descriptor := SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i
      CompletedEdgeMachine.budget hq large descriptor source (tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars + 3 +
      budget signs ids vars source work countTape base indices (next hq large descriptor ids vars data)

def sequenceInTime (selectSigns : A → SignTuple branch n t)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ i, Function.Injective (source i))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ i, source i 4 = work 5) (sharedOutput : ∀ i, source i 5 = work 9)
    (sourceAvoid : ∀ i field j, KeyMetadataMachine.idTape (source i) field ≠ work j)
    (countTape : K) (countAvoid : ∀ j, countTape ≠ work j)
    (sourceCount : ∀ i field, KeyMetadataMachine.idTape (source i) field ≠ countTape)
    (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large))
    (atLabels : ∀ l, program (labels l) =
      instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns source work countTape
        indices labels exit rejected l)
    (base : K → List Bool) (ambient : A)
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (source i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids i) (vars i) field))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = [])
    (data : Data width) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows indices labels exit,
        SignedDescriptorStageMachine.clean hq large ambient, tapes work countTape base data⟩
      (some ⟨exit, SignedDescriptorStageMachine.clean hq large ambient,
        tapes work countTape base
          (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) ids vars indices data)⟩)
      (budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) ids vars source work countTape base
        indices data) := by
  induction indices generalizing data with
  | nil =>
    exact {
      steps := 0
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl _
    }
  | cons i indices ih =>
    let descriptor := SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i
    have hd (j k : Fin 10) (hne : j ≠ k) : work j ≠ work k :=
      fun h => hne (workDistinct h)
    have currentSource (position : Fin width) (field : Fin 4) :
        tapes work countTape base data (KeyMetadataMachine.idTape (source position) field) =
          encodeWord (KeyMetadataMachine.fieldValue (ids position) (vars position) field) := by
      rw [tapes_frame work countTape base data _ (sourceCount position field)
        (sourceAvoid position field 1) (sourceAvoid position field 8) (sourceAvoid position field 7)]
      exact sourceWords position field
    have currentEmpty (j : Fin 10) (h1 : j ≠ 1) (h7 : j ≠ 7) (h8 : j ≠ 8) :
        tapes work countTape base data (work j) = [] := by
      rw [tapes_frame work countTape base data _ (Ne.symm (countAvoid j))
        (hd j 1 h1) (hd j 8 h8) (hd j 7 h7)]
      exact empty j h1 h7 h8
    have leftDictionary : tapes work countTape base data (work 1) =
        BinaryNameSearch.stream (CanonicalVertexNames.tokens data.leftKeys) := by
      simp [tapes, Ne.symm (countAvoid 1), hd 1 8 (by decide), hd 1 7 (by decide)]
    have rightDictionary : tapes work countTape base data (work 8) =
        BinaryNameSearch.stream (CanonicalVertexNames.tokens data.rightKeys) := by
      simp [tapes, Ne.symm (countAvoid 8), hd 8 7 (by decide)]
    have first := SignedDescriptorStageMachine.stageInTime (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
      ids vars source sourceDistinct work workDistinct sharedScratch sharedOutput sourceAvoid
      countTape (fun l => labels (.inl l))
      (entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows indices (fun l => labels (.inr l)) exit) rejected
      program (fun l => atLabels (.inl l)) (tapes work countTape base data) ambient
      data.leftKeys data.rightKeys currentSource leftDictionary rightDictionary currentEmpty
    rw [finalTapes_eq hq large descriptor ids vars work workDistinct countTape countAvoid base data]
      at first
    have rest := ih (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
      (next hq large descriptor ids vars data)
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first rest
    refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simpa only [entry, MachineFiniteSequence.entry, localMain, result]
        using joined.evals_in_steps
    · change joined.steps ≤
        (CompletedEdgeMachine.budget hq large descriptor source (tapes work countTape base data)
          data.leftKeys data.rightKeys ids vars + 3) +
        budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient)
          ids vars source work countTape base indices (next hq large descriptor ids vars data)
      exact joined.steps_le_m.trans (Nat.le_of_eq (Nat.add_comm _ _))

theorem result_count (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (indices : List (Fin D)) (data : Data width) :
    (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs ids vars indices data).count =
      data.count + indices.length := by
  induction indices generalizing data with
  | nil => simp [result]
  | cons i indices ih =>
      simp only [result, ih, next, List.length_cons]
      omega

theorem result_leftKeys (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (indices : List (Fin D)) (data : Data width) :
    (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs ids vars indices data).leftKeys =
      data.leftKeys ++ indices.map (fun i => CompletedEdgeMachine.key hq large
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i) .left ids vars) := by
  induction indices generalizing data with
  | nil => simp [result]
  | cons i indices ih => simp only [result, ih, next, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append]

theorem result_rightKeys (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (indices : List (Fin D)) (data : Data width) :
    (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs ids vars indices data).rightKeys =
      data.rightKeys ++ indices.map (fun i => CompletedEdgeMachine.key hq large
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i) .right ids vars) := by
  induction indices generalizing data with
  | nil => simp [result]
  | cons i indices ih => simp only [result, ih, next, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append]

def blocks (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) : List (Fin D) → Data width → List (List Bool)
  | [], _ => []
  | i :: indices, data =>
      let descriptor := SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs i
      CompletedEdgeMachine.edgeBits hq large descriptor data.leftKeys data.rightKeys ids vars ::
        blocks signs ids vars indices (next hq large descriptor ids vars data)

theorem result_output (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (indices : List (Fin D)) (data : Data width) :
    (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs ids vars indices data).reversedOutput =
      ((blocks hq large hn hbranch hrows signs ids vars indices data).flatten).reverse ++
        data.reversedOutput := by
  induction indices generalizing data with
  | nil => simp [result, blocks]
  | cons i indices ih =>
      simp only [result, ih, blocks, next, List.flatten_cons, List.reverse_append,
        List.append_assoc]

def allStages : List (Fin D) := List.ofFn id

def tupleResult (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) : Data width :=
  result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (SourceTupleScheduleMachine.sourceSigns formula indices)
    (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
    (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) data

private theorem bodyBudgetOrder (preparation edges cleanup : Nat) :
    1 + (cleanup + (edges + (preparation + 1))) ≤
      1 + preparation + edges + cleanup + 1 := by
  omega

section WholeBody

variable {Extra U : Type} [DecidableEq Extra] [Fintype U] [DecidableEq U]

local notation "Arena" => Tape width Extra
local notation "Control" => BodyState (rows := rows) (repeats := repeats) hq large U
local notation "WholeLabel" => BodyLabel width D Desc Extra

def bodyMain : WholeLabel := .start

def bodySigns (control : SourceTupleMachine.State width U) : SignTuple branch n t :=
  SourceTupleScheduleMachine.signTuple control.1.1.2

omit [Fintype U] [DecidableEq U] in
@[simp] theorem bodySigns_prepared
    (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (ambient : U) :
    bodySigns (SignedTupleLayout.preparedSource formula indices ambient) =
      SourceTupleScheduleMachine.sourceSigns formula indices := rfl

def bodyExit (exit : Option Λ) : TM2.Stmt (fun _ : Arena => Bool) Λ Control :=
  match exit with
  | none => .halt
  | some label => .goto (fun _ => label)

def cleanupEntry (labels : WholeLabel → Λ) : Option Λ :=
  SignedTupleCleanupMachine.entry (fun l => labels (.cleanup l)) (some (labels .reset))

def edgesEntry (labels : WholeLabel → Λ) : Option Λ :=
  entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows)
    (fun l => labels (.edges l)) (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels)

def bodyInstruction (labels : WholeLabel → Λ) (exit : Option Λ) :
    WholeLabel → TM2.Stmt (fun _ : Arena => Bool) Λ Control
  | .start => bodyExit hq large
      (SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
        (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels))
  | .prepare label => SignedTuplePreparationMachine.instruction
      (fun l => labels (.prepare l)) (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) label
  | .edges label => instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows bodySigns
      SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows)
      (fun l => labels (.edges l)) (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) none label
  | .cleanup label => SignedTupleCleanupMachine.instruction
      (fun l => labels (.cleanup l)) (some (labels .reset)) label
  | .reset => .load (fun control => SignedTupleLayout.clean control.1.1.1.1.1.1)
      (bodyExit hq large exit)

def nativeProgram : WholeLabel → TM2.Stmt (fun _ : Arena => Bool) WholeLabel Control :=
  bodyInstruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows id none

theorem tapes_input (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (data : Data width) :
    SignedTupleLayout.Input formula indices (tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data) := by
  refine {
    toClear := {
      rawDigits := ?_
      rawVariables := ?_
      sourceWork := ?_
      encodedVariables := ?_
      scratch := ?_
    }
    table := ?_
    current := ?_
  }
  · intro i
    simpa [tapes] using input.rawDigits i
  · intro i j
    simpa [tapes] using input.rawVariables i j
  · intro j
    simpa [tapes] using input.sourceWork j
  · intro i j
    simpa [tapes] using input.encodedVariables i j
  · simpa [tapes] using input.scratch
  · simpa [tapes] using input.table
  · intro i
    simpa [tapes] using input.current i

theorem prepared_tapes_commute (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (data : Data width) :
    SignedTupleLayout.preparedTapes formula indices (tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data) =
      tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount (SignedTupleLayout.preparedTapes formula indices base) data := by
  funext tape
  cases tape with
  | source source => cases source <;> simp [SignedTupleLayout.preparedTapes, tapes]
  | current i => simp [SignedTupleLayout.preparedTapes, tapes]
  | remaining i => simp [SignedTupleLayout.preparedTapes, tapes]
  | encodedVariable i j => simp [SignedTupleLayout.preparedTapes, tapes]
  | adapterScratch => simp [SignedTupleLayout.preparedTapes, tapes]
  | edgeWork j => simp [SignedTupleLayout.preparedTapes, tapes, Function.update_apply]
  | edgeCount => simp [SignedTupleLayout.preparedTapes, tapes]
  | extra value => simp [SignedTupleLayout.preparedTapes, tapes]

def bodyBudget (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (data : Data width) : Nat :=
  1 + SignedTuplePreparationMachine.budget width (SourceOccurrenceEncoding.bits formula).length +
    budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (SourceTupleScheduleMachine.sourceSigns formula indices)
      (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
      SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
      (SignedTupleLayout.preparedTapes formula indices base) (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) data +
    7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) + 1

def bodyInTime (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U) (data : Data width)
    (labels : WholeLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Arena => Bool) Λ Control)
    (atLabels : ∀ label, program (labels label) = bodyInstruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels exit label)
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (.edgeWork j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (bodyMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows)), SignedTupleLayout.clean ambient,
        tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data⟩
      (some ⟨exit, SignedTupleLayout.clean ambient,
        tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base (tupleResult (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices data)⟩)
      (bodyBudget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices base data) := by
  let initialTapes := tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data
  let finalData := tupleResult (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices data
  let finalTapes := tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base finalData
  let prepared := SignedTupleLayout.preparedTapes formula indices base
  let sourceControl := SignedTupleLayout.preparedSource formula indices ambient
  have startRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .start), SignedTupleLayout.clean ambient, initialTapes⟩
      (some ⟨SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
        (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels),
        SignedTupleLayout.clean ambient, initialTapes⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .start)) (SignedTupleLayout.clean ambient) initialTapes) = _
    rw [atLabels .start]
    change some (TM2.stepAux (bodyExit hq large _) (SignedTupleLayout.clean ambient) initialTapes) = _
    cases SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
      (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) <;> rfl
  have prepareRun := SignedTuplePreparationMachine.prepareInTime formula indices initialTapes
    (tapes_input formula indices base input data) ambient
    (fun l => labels (.prepare l)) (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels)
    program (fun l => atLabels (.prepare l))
  dsimp only [initialTapes] at prepareRun
  rw [prepared_tapes_commute] at prepareRun
  have sourceAvoid : ∀ (i : Fin width) (field : Fin 4) (j : Fin 10),
      KeyMetadataMachine.idTape (SignedTupleLayout.metadata (Extra := Extra) i) field ≠ SignedTupleLayout.Tape.edgeWork j := by
    intro i field j
    fin_cases field <;> simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  have sourceCount : ∀ (i : Fin width) (field : Fin 4),
      KeyMetadataMachine.idTape (SignedTupleLayout.metadata (Extra := Extra) i) field ≠ SignedTupleLayout.Tape.edgeCount := by
    intro i field
    fin_cases field <;> simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  have edgesRun := sequenceInTime (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows bodySigns
    (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
    SignedTupleLayout.metadata SignedTupleLayout.metadata_injective
    SignedTupleLayout.Tape.edgeWork (by intro i j h; cases h; rfl) (fun _ => rfl) (fun _ => rfl) sourceAvoid
    SignedTupleLayout.Tape.edgeCount (by intro j; simp) sourceCount
    (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) (fun l => labels (.edges l))
    (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) none program
    (fun l => atLabels (.edges l)) prepared sourceControl
    (SignedTupleLayout.prepared_metadata formula indices base input)
    (by intro j h1 h7 h8; exact empty j h1 h7 h8) data
  have signsEq : bodySigns (branch := branch) (n := n) (t := t) sourceControl =
      SourceTupleScheduleMachine.sourceSigns (branch := branch) (n := n) (t := t) formula indices :=
    bodySigns_prepared (branch := branch) (n := n) (t := t) formula indices ambient
  have resultEq :
      result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows (bodySigns sourceControl)
        (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
        (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
          hn hbranch hrows) data = finalData := by
    rw [signsEq]
    rfl
  have stateEq : SignedDescriptorStageMachine.clean (branch := branch) (n := n) (t := t)
      (q := q) (rows := rows) (repeats := repeats) hq large sourceControl =
      SignedTupleLayout.preparedState («Desc» := Desc) formula indices ambient := rfl
  rw [stateEq, resultEq] at edgesRun
  have cleanupRun := SignedTupleCleanupMachine.cleanupInTime formula indices finalTapes
    (tapes_input formula indices base input finalData) ambient
    (fun l => labels (.cleanup l)) (some (labels .reset)) program (fun l => atLabels (.cleanup l))
  have cleanupDecider : (fun a b : Extra => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq Extra) := Subsingleton.elim _ _
  rw [cleanupDecider] at cleanupRun
  dsimp only [finalTapes] at cleanupRun
  rw [prepared_tapes_commute] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reset), SignedTupleLayout.preparedState formula indices ambient, finalTapes⟩
      (some ⟨exit, SignedTupleLayout.clean ambient, finalTapes⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .reset))
      (SignedTupleLayout.preparedState formula indices ambient) finalTapes) = _
    rw [atLabels .reset]
    cases exit <;> rfl
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
        (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ startRun prepareRun)
        edgesRun) cleanupRun) resetRun
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [bodyMain, tupleResult, finalData, finalTapes, initialTapes,
      prepared, sourceControl, bodySigns_prepared] using joined.evals_in_steps
  · have bounded := joined.steps_le_m.trans (bodyBudgetOrder _ _ _)
    simpa only [bodyBudget, prepared, sourceControl, bodySigns_prepared] using bounded

end WholeBody

end
end PerfectCompleteness.SignedTupleBodyMachine

end OAI

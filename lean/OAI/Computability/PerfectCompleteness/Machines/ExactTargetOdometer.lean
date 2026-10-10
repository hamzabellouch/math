import OAI.Computability.PerfectCompleteness.Foundations.SignedTupleSemantics
import OAI.Computability.PerfectCompleteness.Machines.SignedRuntimeBounds
import OAI.Computability.PerfectCompleteness.Machines.SignedTupleBodyMachine
import OAI.Computability.PerfectCompleteness.Machines.SourceOccurrenceProducerLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletedVisitOrder
import OAI.Computability.UniqueGames.Machines.MachineTupleOdometer

namespace OAI


namespace PerfectCompleteness.ExactTargetOdometer


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {width radix : Nat}

def setCoordinate (digits : Fin width → Fin radix) (depth : Nat) (value : Fin radix) :
    Fin width → Fin radix :=
  fun i => if i.val = depth then value else digits i

@[simp] theorem setCoordinate_self (digits : Fin width → Fin radix)
    (i : Fin width) (value : Fin radix) :
    setCoordinate digits i.val value i = value := by
  simp [setCoordinate]

theorem setCoordinate_eq_update (digits : Fin width → Fin radix)
    (coordinate : Fin width) (value : Fin radix) :
    setCoordinate digits coordinate.val value = Function.update digits coordinate value := by
  funext i
  by_cases same : i = coordinate
  · subst i
    simp [setCoordinate]
  · have different : i.val ≠ coordinate.val := fun h => same (Fin.ext h)
    simp [setCoordinate, same, different]

theorem setCoordinate_zero (digits : Fin width → Fin radix) (depth : Nat)
    (positive : 0 < radix) (zero : ∀ i, i.val = depth → (digits i).val = 0) :
    setCoordinate digits depth ⟨0, positive⟩ = digits := by
  funext i
  by_cases same : i.val = depth
  · simp only [setCoordinate, ite_eq_left same]
    apply Fin.ext
    exact (zero i same).symm
  · simp [setCoordinate, same]

def fillCoordinates (digits : Fin width → Fin radix) {depth : Nat}
    (tuple : Fin depth → Fin radix) : Fin width → Fin radix :=
  fun i => if h : i.val < depth then tuple ⟨i.val, h⟩ else digits i

@[simp] theorem fillCoordinates_zero (digits : Fin width → Fin radix)
    (tuple : Fin 0 → Fin radix) : fillCoordinates digits tuple = digits := by
  funext i
  simp [fillCoordinates]

@[simp] theorem fillCoordinates_all (digits : Fin width → Fin radix)
    (tuple : Fin width → Fin radix) : fillCoordinates digits tuple = tuple := by
  funext i
  simp [fillCoordinates, i.isLt]

theorem fillCoordinates_snoc (digits : Fin width → Fin radix) {depth : Nat}
    (tuple : Fin depth → Fin radix) (value : Fin radix) :
    fillCoordinates digits (Fin.snoc tuple value) =
      fillCoordinates (setCoordinate digits depth value) tuple := by
  funext i
  by_cases hi : i.val < depth
  · have hi' : i.val < depth + 1 := by omega
    simp [fillCoordinates, hi, hi', Fin.snoc]
  · by_cases same : i.val = depth
    · simp [fillCoordinates, Fin.snoc, setCoordinate, same]
    · have hi' : ¬ i.val < depth + 1 := by omega
      simp [fillCoordinates, hi, hi', setCoordinate, same]

def visits : Nat → (Fin width → Fin radix) → List (Fin width → Fin radix)
  | 0, digits => [digits]
  | depth + 1, digits => (List.ofFn (fun value : Fin radix => value)).flatMap
      (fun value => visits depth (setCoordinate digits depth value))

theorem visits_eq_tupleOrder (depth : Nat) (digits : Fin width → Fin radix) :
    visits depth digits = (MachineTupleOdometer.tupleOrder radix depth).map
      (fillCoordinates digits) := by
  induction depth generalizing digits with
  | zero =>
      simp only [visits, MachineTupleOdometer.tupleOrder_dimension_zero,
        List.map_cons, List.map_nil, fillCoordinates_zero]
  | succ depth ih =>
      rw [visits, MachineTupleOdometer.tupleOrder_snoc, List.map_flatMap]
      apply List.flatMap_congr
      intro value _
      rw [ih, List.map_map]
      apply List.map_congr_left
      intro tuple _
      exact (fillCoordinates_snoc digits tuple value).symm

@[simp] theorem visits_all (digits : Fin width → Fin radix) :
    visits width digits = MachineTupleOdometer.tupleOrder radix width := by
  have identity : fillCoordinates digits =
      (id : (Fin width → Fin radix) → (Fin width → Fin radix)) := by
    funext tuple
    exact fillCoordinates_all digits tuple
  rw [visits_eq_tupleOrder, identity, List.map_id]

def foldVisits {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (depth : Nat) (digits : Fin width → Fin radix) (initial : P) : P :=
  (visits depth digits).foldl (fun data tuple => step tuple data) initial

@[simp] theorem foldVisits_zero {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (digits : Fin width → Fin radix) (initial : P) :
    foldVisits step 0 digits initial = step digits initial := rfl

def blockPrefix {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (depth : Nat) (digits : Fin width → Fin radix) (count : Nat) (initial : P) : P :=
  ((List.ofFn (fun value : Fin radix => value)).take count).foldl
    (fun data value => foldVisits step depth (setCoordinate digits depth value) data) initial

@[simp] theorem blockPrefix_zero {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (depth : Nat) (digits : Fin width → Fin radix) (initial : P) :
    blockPrefix step depth digits 0 initial = initial := rfl

theorem blockPrefix_succ {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (depth : Nat) (digits : Fin width → Fin radix) (value : Fin radix) (initial : P) :
    blockPrefix step depth digits (value.val + 1) initial =
      foldVisits step depth (setCoordinate digits depth value)
        (blockPrefix step depth digits value.val initial) := by
  have inside : value.val < (List.ofFn (fun value : Fin radix => value)).length := by
    simpa only [List.length_ofFn] using value.isLt
  simp only [blockPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_ofFn]

@[simp] theorem blockPrefix_all {P : Type*} (step : (Fin width → Fin radix) → P → P)
    (depth : Nat) (digits : Fin width → Fin radix) (initial : P) :
    blockPrefix step depth digits radix initial = foldVisits step (depth + 1) digits initial := by
  have complete : (List.ofFn (fun value : Fin radix => value)).take radix =
      List.ofFn (fun value : Fin radix => value) :=
    List.take_of_length_le (by simp)
  simp only [blockPrefix, complete, foldVisits, visits, List.foldl_flatMap]

variable {branch : Nat → Nat} {n t v m : Nat}

theorem visits_sourceOrder
    (digits : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    (visits (TreeCanonical.locationCount branch n t) digits).map
        SourceQuestionOrder.tupleToQuestion = SourceVisitOrder.visitOrder branch n t m := by
  rw [visits_all, SourceVisitOrder.visitOrder_eq_tupleOrder]

variable (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

theorem visits_completedOrder
    (digits : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    (visits (TreeCanonical.locationCount branch n t) digits).flatMap
        (fun tuple => CompletedVisitOrder.localOrder clauses rows repeats hn hbranch hrows δ
          (SourceQuestionOrder.tupleToQuestion tuple)) =
      CompletedVisitOrder.completedOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  rw [CompletedVisitOrder.completedOrder, ← visits_sourceOrder digits, List.flatMap_map]

end

noncomputable section

variable {width : Nat} {Extra : Type}

def baseTapes (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) : SignedTupleLayout.Tape width Extra → List Bool
  | .source .table => NormalizedSourceInput.bits input
  | .current i => encodeWord (indices i).val
  | .remaining i => encodeWord (NormalizedSourceInput.clauseCount input - 1 - (indices i).val)
  | .extra x => extra x
  | _ => []

theorem baseTapes_input (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) :
    SignedTupleLayout.Input input.formula indices (baseTapes input indices extra) where
  toClear := {
    rawDigits := fun _ => rfl
    rawVariables := fun _ _ => rfl
    sourceWork := fun _ => rfl
    encodedVariables := fun _ _ => rfl
    scratch := rfl
  }
  table := rfl
  current := fun _ => rfl

@[simp] theorem baseTapes_edgeWork (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) (j : Fin 10) :
    baseTapes input indices extra (.edgeWork j) = [] := rfl

theorem baseTapes_emptyWork (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) :
    ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 →
      baseTapes input indices extra (.edgeWork j) = [] := by
  intro j _ _ _
  rfl


variable {branch : Nat → Nat} {n t : Nat} [DecidableEq Extra]

local notation "W" => TreeCanonical.locationCount branch n t

def nativeTapes (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    SignedTupleLayout.Tape W Extra → List Bool :=
  SignedTupleBodyMachine.tapes (branch := branch) (n := n) (t := t)
    SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
    (baseTapes input indices extra) data

@[simp] theorem nativeTapes_table (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra (.source .table) = NormalizedSourceInput.bits input := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_current (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (i : Fin W) :
    nativeTapes input indices data extra (.current i) = encodeWord (indices i).val := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_remaining (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (i : Fin W) :
    nativeTapes input indices data extra (.remaining i) =
      encodeWord (NormalizedSourceInput.clauseCount input - 1 - (indices i).val) := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_output (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra (.edgeWork 7) = data.reversedOutput := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes]

@[simp] theorem nativeTapes_count (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra .edgeCount = encodeWord data.count := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes]

@[simp] theorem nativeTapes_extra (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (x : Extra) :
    nativeTapes input indices data extra (.extra x) = extra x := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

theorem nativeTapes_input (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    SignedTupleLayout.Input input.formula indices (nativeTapes input indices data extra) := by
  exact SignedTupleBodyMachine.tapes_input (branch := branch) (n := n) (t := t)
    input.formula indices (baseTapes input indices extra)
    (baseTapes_input input indices extra) data

theorem nativeTapes_emptyWork (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool)
    (j : Fin 10) (h1 : j ≠ 1) (h7 : j ≠ 7) (h8 : j ≠ 8) :
    nativeTapes input indices data extra (.edgeWork j) = [] := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, h1, h7, h8]

theorem digitTapes_nativeTapes (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool)
    (coordinate : Fin W) (value : Fin (NormalizedSourceInput.clauseCount input)) :
    MachineTupleOdometer.digitTapes
        (SignedTupleLayout.Tape.current coordinate)
        (SignedTupleLayout.Tape.remaining coordinate)
        (nativeTapes input indices data extra)
        value.val (NormalizedSourceInput.clauseCount input - 1 - value.val) [] [] =
      nativeTapes input (Function.update indices coordinate value) data extra := by
  funext tape
  cases tape with
  | source source =>
      cases source <;>
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | current position =>
      by_cases same : position = coordinate
      · subst position
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
      · simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, same]
  | remaining position =>
      by_cases same : position = coordinate
      · subst position
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
      · simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, same]
  | encodedVariable position slot =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | adapterScratch =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | edgeWork j =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, Function.update_apply]
  | edgeCount =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes]
  | extra x =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

end

inductive Label (locations stages : Nat) (Descriptor Extra : Type)
  | body (label : SignedTupleBodyMachine.BodyLabel locations stages Descriptor Extra)
  | check (coordinate : Fin locations)
  | reset (coordinate : Fin locations)
  | exit
  deriving DecidableEq, Fintype

noncomputable section Native

variable {branch : Nat → Nat} {n t : Nat}
  (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "Desc" => SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large

abbrev Control := SignedTupleLayout.State width Unit Desc
abbrev Ambient := (SourceTupleMachine.State width Unit × Option Desc) × (Bool × Option Bool)
abbrev NativeLabel (Extra : Type) := Label width D Desc Extra

variable {Extra : Type} [DecidableEq Extra]

local notation "Arena" => SignedTupleLayout.Tape width Extra
local notation "Labels" => NativeLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ Extra
local notation "Registers" => Control (branch := branch) (n := n) (t := t) rows repeats δ

def checkAt (depth : Nat) : Labels :=
  if h : depth < width then .check ⟨depth, h⟩ else .exit

def resetAt (depth : Nat) : Labels :=
  if h : depth < width then .reset ⟨depth, h⟩ else .exit

def currentAt (depth : Nat) : Arena :=
  if h : depth < width then .current ⟨depth, h⟩ else .adapterScratch

def remainingAt (depth : Nat) : Arena :=
  if h : depth < width then .remaining ⟨depth, h⟩ else .edgeCount

def body : Labels := .body .start

def program : Labels → Turing.TM2.Stmt (fun _ : Arena => Bool) Labels Registers
  | .body label => SignedTupleBodyMachine.bodyInstruction (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
      Label.body (some (checkAt (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ 0)) label
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (body (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i) (.reset i)
      (checkAt (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ (i.val + 1))
  | .exit => .halt

def tupleStep (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) : SignedTupleBodyMachine.Data width :=
  SignedTupleBodyMachine.result (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    (MetadataFreeSampler.sourceSigns (NormalizedSourceInput.clauses input)
      (SourceQuestionOrder.tupleToQuestion indices))
    (fun i => (indices i).val)
    (fun i slot => ((NormalizedSourceInput.clauses input) (indices i)).variable slot |>.val)
    (List.ofFn (fun i : Fin D => i)) data

@[simp] theorem tupleStep_count (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) :
    (tupleStep rows repeats hn hbranch hrows δ input indices data).count = data.count + D := by
  simp only [tupleStep, SignedTupleBodyMachine.result_count, List.length_ofFn]

theorem tupleStep_eq (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) :
    tupleStep rows repeats hn hbranch hrows δ input indices data =
      SignedTupleBodyMachine.tupleResult (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices data := rfl

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "entry" => body (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atCheck" => checkAt (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atReset" => resetAt (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atCurrent" => currentAt (branch := branch) (n := n) (t := t) (Extra := Extra)
local notation "atRemaining" => remainingAt (branch := branch) (n := n) (t := t) (Extra := Extra)

def configuration (label : Labels) (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) :
    Turing.TM2.Cfg (fun _ : Arena => Bool) Labels Registers :=
  ⟨some label, SignedTupleLayout.clean (), nativeTapes input indices data extra⟩

local notation "cfg" => configuration rows repeats hn hbranch hrows δ

def leafBudget (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) : Nat :=
  SignedTupleBodyMachine.bodyBudget (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats)
    hq large hn hbranch hrows
    input.formula indices (baseTapes input indices extra) data

def leafInTime (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime (Turing.TM2.step runProgram)
      (cfg entry input indices data extra)
      (some (cfg (atCheck 0) input indices
        (tupleStep rows repeats hn hbranch hrows δ input indices data) extra))
      (leafBudget rows repeats hn hbranch hrows δ input indices data extra) := by
  have run := SignedTupleBodyMachine.bodyInTime (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    input.formula indices (baseTapes input indices extra) (baseTapes_input input indices extra)
    () data Label.body (some (atCheck 0)) runProgram (fun _ => rfl)
    (baseTapes_emptyWork input indices extra)
  simpa only [configuration, body, SignedTupleBodyMachine.bodyMain, nativeTapes,
    tupleStep_eq, leafBudget] using run

def maxLeafBudget (input : NormalizedSourceInput.Input) (extra : Extra → List Bool) :
    Nat → (Fin width → Fin (NormalizedSourceInput.clauseCount input)) →
      SignedTupleBodyMachine.Data width → Nat
  | 0, indices, data => leafBudget rows repeats hn hbranch hrows δ input indices data extra
  | depth + 1, indices, data => Finset.univ.sup fun value =>
      maxLeafBudget input extra depth (setCoordinate indices depth value)
        (blockPrefix (tupleStep rows repeats hn hbranch hrows δ input) depth indices value.val data)

def CostsAtMost (input : NormalizedSourceInput.Input) (extra : Extra → List Bool) (B : Nat) :
    Nat → (Fin width → Fin (NormalizedSourceInput.clauseCount input)) →
      SignedTupleBodyMachine.Data width → Prop
  | 0, indices, data => leafBudget rows repeats hn hbranch hrows δ input indices data extra ≤ B
  | depth + 1, indices, data => ∀ value,
      CostsAtMost input extra B depth (setCoordinate indices depth value)
        (blockPrefix (tupleStep rows repeats hn hbranch hrows δ input) depth indices value.val data)

theorem costsAtMost_of_max (input : NormalizedSourceInput.Input) (extra : Extra → List Bool)
    (depth : Nat) (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (B : Nat)
    (bounded : maxLeafBudget rows repeats hn hbranch hrows δ input extra depth indices data ≤ B) :
    CostsAtMost rows repeats hn hbranch hrows δ input extra B depth indices data := by
  induction depth generalizing indices data with
  | zero => exact bounded
  | succ depth ih =>
      intro value
      apply ih
      exact (Finset.le_sup (Finset.mem_univ value)).trans bounded

private theorem digitTapes_at (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool)
    (depth remainder : Nat) (inside : depth < width)
    (remainingBound : remainder ≤ NormalizedSourceInput.clauseCount input - 1) :
    MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
        (nativeTapes input indices data extra)
        (NormalizedSourceInput.clauseCount input - 1 - remainder) remainder [] [] =
      nativeTapes input (setCoordinate indices depth
        ⟨NormalizedSourceInput.clauseCount input - 1 - remainder,
          by have := NormalizedSourceInput.clauseCount_positive input; omega⟩) data extra := by
  have positive := NormalizedSourceInput.clauseCount_positive input
  have valueBound : NormalizedSourceInput.clauseCount input - 1 - remainder <
      NormalizedSourceInput.clauseCount input := by omega
  have complement : NormalizedSourceInput.clauseCount input - 1 -
      (NormalizedSourceInput.clauseCount input - 1 - remainder) = remainder := by omega
  have h := digitTapes_nativeTapes input indices data extra ⟨depth, inside⟩
    ⟨NormalizedSourceInput.clauseCount input - 1 - remainder, valueBound⟩
  simpa only [currentAt, remainingAt, dite_eq_left inside, complement,
    ← setCoordinate_eq_update] using h

theorem existsTree (input : NormalizedSourceInput.Input) (extra : Extra → List Bool)
    (B depth : Nat) (inside : depth ≤ width)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (zero : ∀ i, i.val < depth → (indices i).val = 0)
    (data : SignedTupleBodyMachine.Data width)
    (costs : CostsAtMost rows repeats hn hbranch hrows δ input extra B depth indices data) :
    ∃ tree : MachineTupleOdometer.NestedCycle (NormalizedSourceInput.clauseCount input)
      atCurrent atRemaining entry atCheck atReset runProgram depth (atCheck depth)
      (cfg entry input indices data extra)
      (cfg (atCheck depth) input indices
        (foldVisits (tupleStep rows repeats hn hbranch hrows δ input) depth indices data) extra),
      tree.LeafBound B := by
  let m := NormalizedSourceInput.clauseCount input
  have positive : 0 < m := NormalizedSourceInput.clauseCount_positive input
  let step := tupleStep (branch := branch) (n := n) (t := t) rows repeats hn hbranch hrows δ input
  induction depth generalizing indices data with
  | zero =>
      let run := leafInTime rows repeats hn hbranch hrows δ input indices data extra
      refine ⟨.leaf (atCheck 0) (cfg entry input indices data extra)
        (cfg (atCheck 0) input indices (foldVisits step 0 indices data) extra)
        run.steps rfl rfl run.evals_in_steps, ?_⟩
      unfold MachineTupleOdometer.NestedCycle.LeafBound
      exact run.steps_le_m.trans costs
  | succ depth ih =>
      have hlt : depth < width := by omega
      let accumulated := blockPrefix step depth indices
      let schedule : MachineTupleOdometer.CycleSchedule Arena (Ambient (branch := branch) (n := n) (t := t) rows repeats δ) :=
        { currentSuffix := []
          remainingSuffix := []
          ambient := fun _ => (SignedTupleLayout.clean («width» := width) («Desc» := Desc) ()).1
          register := fun _ => none
          base := fun remainder => nativeTapes input indices (accumulated (m - remainder) data) extra }
      have children : ∀ r : Fin m,
          ∃ tree : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
            atReset runProgram depth (atCheck depth)
            (MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base)
            (MachineTupleOdometer.checkConfiguration (atCurrent depth) (atRemaining depth)
              (atCheck depth) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
        intro r
        have hr : r.val ≤ m - 1 := by omega
        let value : Fin m := ⟨m - 1 - r.val, by omega⟩
        have before : m - (r.val + 1) = value.val := by dsimp [value]; omega
        have after : m - r.val = value.val + 1 := by dsimp [value]; omega
        have childZero : ∀ i, i.val < depth →
            (setCoordinate indices depth value i).val = 0 := by
          intro i hi
          simp only [setCoordinate, ite_eq_right (by omega : i.val ≠ depth)]
          exact zero i (by omega)
        have childCosts : CostsAtMost rows repeats hn hbranch hrows δ input extra B depth
            (setCoordinate indices depth value) (accumulated (m - (r.val + 1)) data) := by
          rw [before]
          exact costs value
        obtain ⟨child, bounded⟩ := ih (by omega) (setCoordinate indices depth value)
          childZero (accumulated (m - (r.val + 1)) data) childCosts
        have outputData : foldVisits step depth (setCoordinate indices depth value)
            (accumulated (m - (r.val + 1)) data) = accumulated (m - r.val) data := by
          rw [before, after]
          exact (blockPrefix_succ step depth indices value data).symm
        have childExists :
            ∃ child : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
              atReset runProgram depth (atCheck depth)
              (cfg entry input (setCoordinate indices depth value)
                (accumulated (m - (r.val + 1)) data) extra)
              (cfg (atCheck depth) input (setCoordinate indices depth value)
                (foldVisits step depth (setCoordinate indices depth value)
                  (accumulated (m - (r.val + 1)) data)) extra), child.LeafBound B :=
          ⟨child, bounded⟩
        rw [outputData] at childExists
        have childStart :
            cfg entry input (setCoordinate indices depth value)
                (accumulated (m - (r.val + 1)) data) extra =
              MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
                entry (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.base := by
          dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
          rw [digitTapes_at input indices _ extra depth r.val hlt hr]
          rfl
        have childFinish :
            cfg (atCheck depth) input (setCoordinate indices depth value)
                (accumulated (m - r.val) data) extra =
              MachineTupleOdometer.checkConfiguration (atCurrent depth) (atRemaining depth)
                (atCheck depth) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.register schedule.base := by
          dsimp only [MachineTupleOdometer.checkConfiguration, schedule, configuration]
          rw [digitTapes_at input indices _ extra depth r.val hlt hr]
          rfl
        rw [childStart, childFinish] at childExists
        exact childExists
      let chosen := fun r => Classical.choose (children r)
      have chosenBound : ∀ r, (chosen r).LeafBound B :=
        fun r => Classical.choose_spec (children r)
      have distinct : atCurrent depth ≠ atRemaining depth := by
        simp [currentAt, remainingAt, hlt]
      have checkInstruction : runProgram (atCheck depth) =
          MachineTupleOdometer.increment (atCurrent depth) (atRemaining depth) entry (atReset depth) := by
        simp [program, checkAt, currentAt, remainingAt, resetAt, hlt]
      have resetInstruction : runProgram (atReset depth) =
          MachineTupleOdometer.reset (atCurrent depth) (atRemaining depth)
            (atReset depth) (atCheck (depth + 1)) := by
        simp [program, resetAt, currentAt, remainingAt, hlt]
      let tree := MachineTupleOdometer.NestedCycle.node depth (atCheck (depth + 1))
        positive distinct checkInstruction resetInstruction schedule chosen
      have treeBound : tree.LeafBound B := by
        simpa only [tree, MachineTupleOdometer.NestedCycle.LeafBound] using chosenBound
      have unchanged : setCoordinate indices depth ⟨0, positive⟩ = indices :=
        setCoordinate_zero indices depth positive (fun i hi => zero i (by omega))
      have startTapes : MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
          (nativeTapes input indices (accumulated (m - ((m - 1) + 1)) data) extra)
          (m - 1 - (m - 1)) (m - 1) [] [] = nativeTapes input indices data extra := by
        rw [digitTapes_at input indices _ extra depth (m - 1) hlt (Nat.le_refl _)]
        have full : m - 1 + 1 = m := by omega
        dsimp only [m] at full unchanged ⊢
        simp only [Nat.sub_self, unchanged, full, accumulated, blockPrefix_zero]
      have finishTapes : MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
          (nativeTapes input indices (accumulated (m - 0) data) extra) 0 (m - 1) [] [] =
          nativeTapes input indices (foldVisits step (depth + 1) indices data) extra := by
        have h := digitTapes_at input indices (accumulated m data) extra depth (m - 1)
          hlt (Nat.le_refl _)
        dsimp only [m] at h unchanged ⊢
        simpa only [Nat.sub_self, Nat.sub_zero, unchanged, accumulated, blockPrefix_all] using h
      have nodeExists :
          ∃ node : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
            atReset runProgram (depth + 1) (atCheck (depth + 1))
            (MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base)
            (MachineTupleOdometer.cycleExit (atCurrent depth) (atRemaining depth)
              (atCheck (depth + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base), node.LeafBound B := ⟨tree, treeBound⟩
      have nodeStart :
          MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base = cfg entry input indices data extra := by
        dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
        rw [startTapes]
        rfl
      have nodeFinish :
          MachineTupleOdometer.cycleExit (atCurrent depth) (atRemaining depth)
              (atCheck (depth + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base =
            cfg (atCheck (depth + 1)) input indices (foldVisits step (depth + 1) indices data) extra := by
        dsimp only [MachineTupleOdometer.cycleExit, schedule, configuration]
        rw [finishTapes]
        rfl
      rw [nodeStart, nodeFinish] at nodeExists
      exact nodeExists

def result (input : NormalizedSourceInput.Input) (data : SignedTupleBodyMachine.Data width) :
    SignedTupleBodyMachine.Data width :=
  foldVisits (tupleStep rows repeats hn hbranch hrows δ input) width
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data

theorem result_count (input : NormalizedSourceInput.Input)
    (data : SignedTupleBodyMachine.Data width) :
    (result rows repeats hn hbranch hrows δ input data).count =
      data.count + NormalizedSourceInput.clauseCount input ^ width * D := by
  have countFold (xs : List (Fin width → Fin (NormalizedSourceInput.clauseCount input)))
      (initial : SignedTupleBodyMachine.Data width) :
      (xs.foldl (fun current indices => tupleStep rows repeats hn hbranch hrows δ input indices current)
        initial).count = initial.count + xs.length * D := by
    induction xs generalizing initial with
    | nil => simp
    | cons indices xs ih =>
        simp only [List.foldl_cons, ih, tupleStep_count, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  unfold result foldVisits
  rw [countFold, visits_all, MachineTupleOdometer.tupleOrder_length]

def enumerateInTime (input : NormalizedSourceInput.Input)
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime (Turing.TM2.step runProgram)
      (cfg entry input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data extra)
      (some (cfg .exit input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)
        (result rows repeats hn hbranch hrows δ input data) extra))
      ((maxLeafBudget rows repeats hn hbranch hrows δ input extra width
        (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data + 2 * width) *
        NormalizedSourceInput.clauseCount input ^ width) := by
  let indices : Fin width → Fin (NormalizedSourceInput.clauseCount input) :=
    fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩
  let B := maxLeafBudget rows repeats hn hbranch hrows δ input extra width indices data
  let witness := existsTree rows repeats hn hbranch hrows δ input extra B width (Nat.le_refl _)
    indices (fun _ _ => rfl) data
    (costsAtMost_of_max rows repeats hn hbranch hrows δ input extra width indices data B (Nat.le_refl _))
  let tree := Classical.choose witness
  have bounded := Classical.choose_spec witness
  refine { steps := tree.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · change (MachineComposition.advance (Turing.TM2.step runProgram))^[tree.steps]
      (some (cfg entry input indices data extra)) = _
    simpa only [checkAt, Nat.lt_irrefl, ↓reduceDIte, result] using tree.trace
  · exact tree.steps_le_power (NormalizedSourceInput.clauseCount_positive input) B bounded

def enumerateInTimeOfBound (input : NormalizedSourceInput.Input)
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) (B : Nat)
    (costs : CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data) :
    StateTransition.EvalsToInTime (Turing.TM2.step runProgram)
      (cfg entry input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data extra)
      (some (cfg .exit input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)
        (result rows repeats hn hbranch hrows δ input data) extra))
      ((B + 2 * width) * NormalizedSourceInput.clauseCount input ^ width) := by
  let witness := existsTree rows repeats hn hbranch hrows δ input extra B width (Nat.le_refl _)
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (fun _ _ => rfl) data costs
  let tree := Classical.choose witness
  have bounded := Classical.choose_spec witness
  refine { steps := tree.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · change (MachineComposition.advance (Turing.TM2.step runProgram))^[tree.steps]
      (some (cfg entry input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data extra)) = _
    simpa only [checkAt, Nat.lt_irrefl, ↓reduceDIte, result] using tree.trace
  · exact tree.steps_le_power (NormalizedSourceInput.clauseCount_positive input) B bounded

end Native

noncomputable section Semantics

theorem foldl_chunks_eq_prefix {α β S : Type*}
    (order : List β) (chunk : α → List β) (step : α → S → S) (pack : List β → S)
    (hstep : ∀ (a : α) (earlier suffix : List β),
      order = earlier ++ chunk a ++ suffix →
        step a (pack earlier) = pack (earlier ++ chunk a))
    (xs : List α) (earlier suffix : List β)
    (split : order = earlier ++ xs.flatMap chunk ++ suffix) :
    xs.foldl (fun state a => step a state) (pack earlier) =
      pack (earlier ++ xs.flatMap chunk) := by
  induction xs generalizing earlier with
  | nil =>
      simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons a xs ih =>
      have currentSplit : order = earlier ++ chunk a ++ (xs.flatMap chunk ++ suffix) := by
        simpa only [List.flatMap_cons, List.append_assoc] using split
      rw [List.foldl_cons, hstep a earlier (xs.flatMap chunk ++ suffix) currentSplit]
      have restSplit : order = (earlier ++ chunk a) ++ xs.flatMap chunk ++ suffix := by
        simpa only [List.flatMap_cons, List.append_assoc] using split
      simpa only [List.flatMap_cons, List.append_assoc] using
        ih (earlier ++ chunk a) restSplit

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "C" => CompletedSignedLaw.Completed (t := t) (NormalizedSourceInput.clauses input)
  rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ

theorem tupleStep_dataOfPrefix
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++
      localOrder (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++
        suffix) :
    ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices
        (pack earlier tail) =
      pack (earlier ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) tail := by
  simpa only [ExactTargetOdometer.tupleStep, List.finRange,
    SignedTupleSemantics.sourceIDs_tuple, SignedTupleSemantics.sourceVariables_tuple] using
      SignedTupleSemantics.full_result_eq (t := t)
        (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)
        earlier suffix tail split

theorem fold_tupleSteps_dataOfPrefix
    (xs : List (Fin width → Fin (NormalizedSourceInput.clauseCount input)))
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) ++ suffix) :
    xs.foldl
        (fun data indices =>
          ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices data)
        (pack earlier tail) =
      pack (earlier ++ xs.flatMap
        (fun indices => localOrder
          (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices))) tail := by
  exact foldl_chunks_eq_prefix order
    (fun indices : Fin width → Fin (NormalizedSourceInput.clauseCount input) =>
      localOrder (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices))
    (ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input)
    (fun before => pack before tail)
    (fun indices before after hsplit =>
      tupleStep_dataOfPrefix rows repeats hn hbranch hrows δ input indices before after tail hsplit)
    xs earlier suffix split

theorem result_dataOfPrefix (tail : List Bool) :
    ExactTargetOdometer.result rows repeats hn hbranch hrows δ input (pack [] tail) =
      pack order tail := by
  let digits : Fin width → Fin (NormalizedSourceInput.clauseCount input) :=
    fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩
  let xs := ExactTargetOdometer.visits width digits
  have chronology : xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) = order :=
    ExactTargetOdometer.visits_completedOrder (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ digits
  have split : order = [] ++ xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) ++ [] := by
    simpa only [List.nil_append, List.append_nil] using chronology.symm
  have folded := fold_tupleSteps_dataOfPrefix rows repeats hn hbranch hrows δ input
    xs [] [] tail split
  change xs.foldl
      (fun data indices =>
        ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices data)
      (pack [] tail) = pack order tail
  simpa only [List.nil_append, chronology] using folded

def targetInTime {Extra : Type} [DecidableEq Extra] (tail : List Bool)
    (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime
      (Turing.TM2.step (program (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ))
      (configuration rows repeats hn hbranch hrows δ
        (body (branch := branch) (n := n) (t := t) (Extra := Extra) rows repeats hn hbranch hrows δ)
        input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) extra)
      (some (configuration rows repeats hn hbranch hrows δ .exit input
        (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack order tail) extra))
      ((maxLeafBudget rows repeats hn hbranch hrows δ input extra width
        (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) + 2 * width) *
        NormalizedSourceInput.clauseCount input ^ width) := by
  simpa only [result_dataOfPrefix] using
    enumerateInTime rows repeats hn hbranch hrows δ input (pack [] tail) extra

end Semantics

noncomputable section ChronologicalCosts

theorem visits_split_at {width radix : Nat} (depth : Nat)
    (indices : Fin width → Fin radix) (value : Fin radix) :
    ExactTargetOdometer.visits (depth + 1) indices =
      ((List.ofFn (fun a : Fin radix => a)).take value.val).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a)) ++
        ExactTargetOdometer.visits depth
          (ExactTargetOdometer.setCoordinate indices depth value) ++
        ((List.ofFn (fun a : Fin radix => a)).drop (value.val + 1)).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a)) := by
  let choices : List (Fin radix) := List.ofFn (fun a : Fin radix => a)
  let lower : Fin radix → List (Fin width → Fin radix) :=
    fun a => ExactTargetOdometer.visits depth (ExactTargetOdometer.setCoordinate indices depth a)
  have inside : value.val < choices.length := by
    simpa only [choices, List.length_ofFn] using value.isLt
  have selected : choices[value.val]'inside = value := by
    simp only [choices, List.getElem_ofFn, Fin.eta]
  have split : choices = choices.take value.val ++ choices.drop value.val :=
    (List.take_append_drop value.val choices).symm
  rw [List.drop_eq_getElem_cons inside, selected] at split
  change choices.flatMap lower =
    (choices.take value.val).flatMap lower ++ lower value ++
      (choices.drop (value.val + 1)).flatMap lower
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using
    congrArg (fun xs : List (Fin radix) => xs.flatMap lower) split

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "Digits" => Fin width → Fin (NormalizedSourceInput.clauseCount input)
local notation "C" => CompletedSignedLaw.Completed (t := t) (NormalizedSourceInput.clauses input)
  rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "step" => ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input

variable {Extra : Type} [DecidableEq Extra]

theorem costsAtMost_of_chronological (extra : Extra → List Bool) (B : Nat) (tail : List Bool)
    (bounded : ∀ (indices : Digits) (before after : List C),
      order = before ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++ after →
      ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack before tail) extra ≤ B)
    (depth : Nat) (indices : Digits) (earlier suffix : List C)
    (split : order = earlier ++ (ExactTargetOdometer.visits depth indices).flatMap
      (fun tuple => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) tuple)) ++ suffix) :
    ExactTargetOdometer.CostsAtMost rows repeats hn hbranch hrows δ input extra B
      depth indices (pack earlier tail) := by
  let chunk : Digits → List C := fun tuple => localOrder
    (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) tuple)
  change order = earlier ++ (ExactTargetOdometer.visits depth indices).flatMap chunk ++ suffix at split
  induction depth generalizing indices earlier suffix with
  | zero =>
      change ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack earlier tail) extra ≤ B
      apply bounded indices earlier suffix
      simpa only [ExactTargetOdometer.visits, List.flatMap_singleton, chunk] using split
  | succ depth ih =>
      intro value
      let beforeTuples : List Digits :=
        ((List.ofFn (fun a : Fin (NormalizedSourceInput.clauseCount input) => a)).take value.val).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a))
      let afterTuples : List Digits :=
        ((List.ofFn (fun a : Fin (NormalizedSourceInput.clauseCount input) => a)).drop
          (value.val + 1)).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a))
      have decomposition : ExactTargetOdometer.visits (depth + 1) indices =
          beforeTuples ++ ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value) ++ afterTuples :=
        visits_split_at depth indices value
      have beforeSplit : order = earlier ++ beforeTuples.flatMap chunk ++
          ((ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value)).flatMap chunk ++
              afterTuples.flatMap chunk ++ suffix) := by
        simpa only [decomposition, List.flatMap_append, List.append_assoc] using split
      have prefixState :
          ExactTargetOdometer.blockPrefix step depth indices value.val (pack earlier tail) =
            pack (earlier ++ beforeTuples.flatMap chunk) tail := by
        have folded := ExactTargetOdometer.fold_tupleSteps_dataOfPrefix
          rows repeats hn hbranch hrows δ input beforeTuples earlier
          ((ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value)).flatMap chunk ++
              afterTuples.flatMap chunk ++ suffix) tail beforeSplit
        simpa only [beforeTuples, ExactTargetOdometer.blockPrefix,
          ExactTargetOdometer.foldVisits, List.foldl_flatMap] using folded
      rw [prefixState]
      apply ih (ExactTargetOdometer.setCoordinate indices depth value)
        (earlier ++ beforeTuples.flatMap chunk) (afterTuples.flatMap chunk ++ suffix)
      simpa only [decomposition, List.flatMap_append, List.append_assoc] using split

theorem costsAtMost_full (extra : Extra → List Bool) (B : Nat) (tail : List Bool)
    (bounded : ∀ (indices : Digits) (before after : List C),
      order = before ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++ after →
      ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack before tail) extra ≤ B) :
    ExactTargetOdometer.CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) := by
  apply costsAtMost_of_chronological rows repeats hn hbranch hrows δ input extra B tail bounded
    width (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) [] []
  simpa only [List.nil_append, List.append_nil] using
    (ExactTargetOdometer.visits_completedOrder (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)).symm

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

def timeBound (size : Nat) : Nat :=
  (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
    (size + 1) ^ (SignedCostEnvelope.degree width + width)

def targetInTimePolynomial (tail : List Bool) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime
      (Turing.TM2.step (program (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ))
      (configuration rows repeats hn hbranch hrows δ
        (body (branch := branch) (n := n) (t := t) (Extra := Extra) rows repeats hn hbranch hrows δ)
        input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) extra)
      (some (configuration rows repeats hn hbranch hrows δ .exit input
        (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack order tail) extra))
      (timeBound (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  let B := SignedCostEnvelope.bodyCoeff width D *
    ((NormalizedSourceInput.bits input).length + 1) ^ SignedCostEnvelope.degree width
  have bounded : CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) := by
    apply costsAtMost_full rows repeats hn hbranch hrows δ input extra B tail
    intro indices before after split
    simpa only [leafBudget] using SignedRuntimeBounds.bodyBudget_le_polynomial (t := t)
      input rows repeats hn hbranch hrows δ indices (baseTapes input indices extra)
      (baseTapes_input input indices extra) before after tail split
  let run := enumerateInTimeOfBound rows repeats hn hbranch hrows δ input
    (pack [] tail) extra B bounded
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [result_dataOfPrefix] using run.evals_in_steps
  · exact run.steps_le_m.trans
      (SignedRuntimeBounds.outerBudget_le_polynomial (t := t) input rows repeats hn hbranch hrows δ)

end ChronologicalCosts
end PerfectCompleteness.ExactTargetOdometer

end OAI

import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineLookupCore
import OAI.Combinatorics.IndependentSets.PCP.Emitter
import OAI.Combinatorics.IndependentSets.PCP.Ambient
import OAI.Combinatorics.IndependentSets.Machines.FinalCNFMachine

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine
open Turing
open PCP
section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := ((σ × Buffer 4096) × Unit) × Option Bool

def readRelationAt (source : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit))

theorem stepAux_readRelationAt (source : K) (exit : Λ) (ambient : σ)
    (buffer : Buffer 4096) (unitState : Unit) (register : Option Bool)
    (relation : GraphTables.RelationTable) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = encodeWords (GraphTables.relationWords relation) ++ suffix) :
    TM2.stepAux (readRelationAt source exit) (((ambient, buffer), unitState), register) tapes =
      ⟨some exit, (((ambient, fun i => relation[i]), unitState), register),
        Function.update tapes source suffix⟩ := by
  change TM2.stepAux (MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit)))
    ((readerStateEquiv σ 4096) (((ambient, unitState), register), buffer)) tapes = _
  rw [MachineControl.stepAux_simulation]
  rw [stepAux_readUnaryAll source _ _ (fun i => relation[i]) tapes suffix
    (by simpa only [unaryBits_relation] using hinput)]
  rfl

end AmbientRelation

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.input, .output, .accumulator, .scratch, .vertices, .darts, .tail, .head, .rowIndex,
    .archive, .reverseIndex, .scanWork, .indexWork}
  complete value := by cases value <;> simp

abbrev Ambient := Unit × Buffer 4096
abbrev Plan := List (Emitter.Command 5 Ambient 36864)

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def headerPlan : Plan :=
  Emitter.affineCommands [(0, 6), (1, 36864)] (fun _ => 0) ++
    Emitter.affineCommands [(1, 40960)] (fun _ => 0)

theorem headerPlan_length : headerPlan.length = 7 := by
  simp [headerPlan]

theorem headerPlan_bits (vertices darts tail head row : Nat) (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords [6 * vertices + 36864 * darts, 40960 * darts] := by
  rw [headerPlan, List.flatMap_append, Emitter.affineCommands_bits,
    Emitter.affineCommands_bits]
  simp [Emitter.affineValue, values, encodeWords]
  rfl

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq

deriving instance Fintype for Label

def guard {hc rc : Nat} (again finish : Label hc rc) :
    TM2.Stmt (fun _ : Tape => Bool) (Label hc rc) (State Unit) :=
  .peek .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (state.1, none)) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => finish)))

def program (headerPlan rowPlan : Plan) :
    Label headerPlan.length rowPlan.length →
      TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan.length rowPlan.length) (State Unit)
  | .copyFirst => Reduction.MachineTransfer.loopAt .input .scratch id false .copyFirst
      (some .copySecond)
  | .copySecond => MachineCopy.forkLoop .scratch .input .archive false .copySecond
      (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart .vertices .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop .input .vertices .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart .darts .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop .input .darts .readDarts (some .seedIndex)
  | .seedIndex => .push .rowIndex (fun _ => false)
      (.push .tail (fun _ => false) (.push .head (fun _ => false)
        (.goto fun _ => .header (Emitter.labelAt headerPlan.length 36864 0 .entry))))
  | .header label => Emitter.statement (Emitter.listCommands headerPlan)
      source .scratch .accumulator Label.header (some .headerClearTail) label
  | .headerClearTail => MachineLookup.discard .tail .headerClearTail .headerClearHead
  | .headerClearHead => MachineLookup.discard .head .headerClearHead .guard
  | .guard => guard .startTail .reverseOutput
  | .startTail => Hastad.SourceMachine.fieldStart .tail .readTail
  | .readTail => Hastad.SourceMachine.fieldLoop .input .tail .readTail (some .startReverse)
  | .startReverse => Hastad.SourceMachine.fieldStart .reverseIndex .readReverse
  | .readReverse => Hastad.SourceMachine.fieldLoop .input .reverseIndex .readReverse
      (some .headTableFirst)
  | .headTableFirst => Reduction.MachineTransfer.loopAt .archive .scratch id false
      .headTableFirst (some .headTableSecond)
  | .headTableSecond => MachineCopy.forkLoop .scratch .archive .scanWork false
      .headTableSecond (some .headIndexFirst)
  | .headIndexFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .headIndexFirst (some .headIndexSecond)
  | .headIndexSecond => MachineCopy.forkLoop .scratch .reverseIndex .indexWork false
      .headIndexSecond (some .headHeaderVertices)
  | .headHeaderVertices => MachineLookup.discard .scanWork .headHeaderVertices .headHeaderDarts
  | .headHeaderDarts => MachineLookup.discard .scanWork .headHeaderDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement 64 .indexWork .scanWork .head Label.headLookup
      (some .readRelation) label
  | .readRelation => readRelationAt .input
      (.row (Emitter.labelAt rowPlan.length 36864 0 .entry))
  | .row label => Emitter.statement (Emitter.listCommands rowPlan)
      source .scratch .accumulator Label.row (some .clearTail) label
  | .clearTail => MachineLookup.discard .tail .clearTail .clearHead
  | .clearHead => MachineLookup.discard .head .clearHead .clearReverse
  | .clearReverse => MachineLookup.discard .reverseIndex .clearReverse .nextRow
  | .nextRow => .push .rowIndex (fun _ => true) (.goto fun _ => .guard)
  | .reverseOutput => Reduction.MachineTransfer.loopAt .accumulator .output id false
      .reverseOutput none

def machine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan.length rowPlan.length
  main := .copyFirst
  σ := State Unit
  initialState := ((((), fun _ => false), ()), none)
  m := program headerPlan rowPlan

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

theorem headRoles_injective : Function.Injective headRoles := by
  decide

def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

def workingTapes (vertices darts row : Nat) (input tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .output => []
  | .accumulator => accumulator
  | .scratch => []
  | .vertices => encodeWord vertices
  | .darts => encodeWord darts
  | .tail => tail
  | .head => head
  | .rowIndex => encodeWord row
  | .archive | .reverseIndex | .scanWork | .indexWork => []

theorem workingTapes_operands (vertices darts row tail head : Nat)
    (input accumulator : List Bool) :
    ∀ i, workingTapes vertices darts row input (encodeWord tail) (encodeWord head)
      accumulator (source i) = encodeWord (values vertices darts tail head row i) := by
  intro i
  fin_cases i <;> rfl

theorem update_working_input (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.input
      replacement = workingTapes vertices darts row replacement tail head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_tail (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.tail
      replacement = workingTapes vertices darts row input replacement head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_head (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.head
      replacement = workingTapes vertices darts row input tail replacement accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_accumulator (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.accumulator
      replacement = workingTapes vertices darts row input tail head replacement := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_rowIndex (vertices darts row : Nat)
    (input tail head accumulator : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.rowIndex
      (true :: encodeWord row) =
      workingTapes vertices darts (row + 1) input tail head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update, encodeWord, List.replicate_succ]

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

end Program

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

end OAI

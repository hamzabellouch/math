import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineLookupDiscard
import OAI.Computability.UniqueGames.PCP.CleanupLemmas
import OAI.Computability.UniqueGames.PCP.Emitter
import OAI.Computability.UniqueGames.PCP.FinalBooleanVerifier
import OAI.Computability.UniqueGames.PCP.GraphTables
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

abbrev Buffer (N : Nat) := MachineFixedBlockMap.Buffer N

section RelationReader

variable {K Λ σ : Type} {N : Nat}

/-- Read fixed register slots from the actual unary 0/1 word encoding. Each
slot consumes one symbol for false and two symbols for true. -/
def readUnarySlots (source : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop source (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop source (fun state _ => state) (readUnarySlots source slots next))
          (readUnarySlots source slots next))

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

theorem unaryBits_length_le (slots : List (Fin N)) (bits : Buffer N) :
    (unaryBits slots bits).length ≤ 2 * slots.length := by
  induction slots with
  | nil => simp [unaryBits]
  | cons i slots ih =>
      have hi : (encodeWord (GraphTables.bitWord (bits i))).length ≤ 2 := by
        cases bits i <;> simp [GraphTables.bitWord, encodeWord_length]
      simp only [unaryBits, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

theorem statementPushBound_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readUnarySlots source slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
      simp only [readUnarySlots, Runtime.statementPushBound, ih, max_self]

variable [DecidableEq K]

/-- Exact stack and register semantics, retaining every unread suffix bit. -/
theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

/-- A fixed table lookup or fixed pattern permutation can follow immediately
after the physical unary decoding, with one genuine finite TM2 transition. -/
def unaryBlockMapAt {M : Nat} (source destination : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readUnarySlots source (List.ofFn id)
    (MachineFixedBlockMap.writeSlots destination (fun state => F state.2)
      (List.ofFn id).reverse
      (.load (fun state => (state.1, MachineFixedBlockMap.emptyBuffer N))
        (MachineFixedBlockMap.finishAt exit)))

theorem stepAux_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (unaryBlockMapAt source destination F exit) state tapes =
      { l := exit, var := (state.1, MachineFixedBlockMap.emptyBuffer N),
        stk := Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination) } := by
  unfold unaryBlockMapAt
  rw [stepAux_readUnaryAll source _ state bits tapes suffix hinput,
    MachineFixedBlockMap.stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]
  cases exit <;> rfl

theorem step_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩ := by
  simp only [TM2.step, atLabel,
    stepAux_unaryBlockMapAt source destination F exit hne state bits tapes suffix hinput]

def unaryBlockInTime {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some label, state, tapes⟩
      (some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩) 1 where
  steps := 1
  evals_in_steps := step_unaryBlockMapAt source destination F exit hne program label
    atLabel state bits tapes suffix hinput
  steps_le_m := Nat.le_refl _

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

/-- Merely rearranges finite registers to match the affine-emitter state.
No tape content or unbounded integer is moved into the internal state. -/
def readerStateEquiv (σ : Type) (N : Nat) :
    (((σ × Unit) × Option Bool) × Buffer N) ≃ (((σ × Buffer N) × Unit) × Option Bool) where
  toFun state := (((state.1.1.1, state.2), state.1.1.2), state.1.2)
  invFun state := (((state.1.1.1, state.1.2), state.2), state.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

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

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .scratch, .vertices,
  .darts, .tail, .head, .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Ambient := Unit × Buffer 4096
abbrev Plan := List (Emitter.Command 5 Ambient 36864)

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

/-- Output variable count and output clause count, in the checked CNF codec. -/
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
  deriving DecidableEq, Fintype

def guard {hc rc : Nat} (again finish : Label hc rc) :
    TM2.Stmt (fun _ : Tape => Bool) (Label hc rc) (State Unit) :=
  .peek .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (state.1, none)) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => finish)))

/-- The actual finite program. All graph-dependent naturals remain on unary
stacks. The only buffered graph data is one fixed 4096-bit relation table. -/
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

/-- The head-access call is part of this concrete program, with its actual
finite labels and framed tape effects. Its data are read from the table. -/
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

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

/-- Structural redirection changes only the destinations of goto and halt. -/
def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

/-- The raw machine has thirteen tapes. These are precisely the twelve
non-output tapes, including the original input and retained archive. -/
def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

abbrev Label (headerPlan rowPlan : Plan) :=
  FinalCNFMachine.Program.Label headerPlan.length rowPlan.length ⊕
    (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (headerPlan rowPlan : Plan) : MachineDrainMany.Label chosen → Label headerPlan rowPlan :=
  fun label => .inr (.inl label)

def resetLabel (headerPlan rowPlan : Plan) : Label headerPlan rowPlan := .inr (.inr ())

def cleanupEntry (headerPlan rowPlan : Plan) : Option (Label headerPlan rowPlan) :=
  MachineDrainMany.entry chosen (cleanupLabel headerPlan rowPlan) (some (resetLabel headerPlan rowPlan))

def completedProgram (headerPlan rowPlan : Plan) : Label headerPlan rowPlan →
    TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan rowPlan) (State Unit)
  | .inl label => redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
      (FinalCNFMachine.Program.program headerPlan rowPlan label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) label
  | .inr (.inr _) => .load (fun _ => (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState) .halt

def completedMachine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan rowPlan
  main := .inl .copyFirst
  σ := State Unit
  initialState := (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState
  m := completedProgram headerPlan rowPlan

def embeddedCfg (headerPlan rowPlan : Plan)
    (cfg : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg) :
    (completedMachine headerPlan rowPlan).Cfg :=
  redirectCfg Sum.inl (cleanupEntry headerPlan rowPlan) cfg

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      erw [stepAux_redirect]
      rfl

@[simp] theorem embedded_init (headerPlan rowPlan : Plan) (input : List Bool) :
    embeddedCfg headerPlan rowPlan (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input) =
      initList (completedMachine headerPlan rowPlan) input := rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

/-- Actual drains followed by a real state-reset instruction reach canonical halt. -/
def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      erw [finalTapes_eq, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- The extra cost is bounded from the actual raw execution, independently of
the contents of its dirty private tapes and finite state. -/
def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

/-- For fixed raw plans, polynomial raw time gives polynomial cleanup time. -/
noncomputable def completedTime (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C 12 * (Polynomial.X + rawTime *
    Polynomial.C (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan)) + 1) + 1

theorem completedTime_eval (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime headerPlan rowPlan rawTime).eval n =
      rawTime.eval n + 12 * (n + rawTime.eval n *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1 := by
  simp [completedTime]

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- Explicit tape frame used during the header phase; all unlisted work tapes
are empty. The archive is separate from the unread input. -/
def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

/-- Exact row-guard handoff: the original table is protected in `archive`,
the output header is accumulated in reverse, and the row index is unary zero. -/
def headerResultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  headerFrame rowsBits (encodeWords [n, m] ++ rowsBits)
    (encodeWord n) (encodeWord m) (encodeWord 0) [] []
    (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

/-- A fixed polynomial in the complete encoded input length. -/
noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

/-- An actual entry-to-guard trace, valid for any unread row suffix and every
finite ambient buffer. No execution premise is supplied by the caller. -/
def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

/-- The unread graph rows in the actual graph codec. -/
def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

/-- Specialization to the entire input of the actual numbered graph codec. -/
def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The same bounded phase begins at the machine's genuine initial configuration. -/
def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI

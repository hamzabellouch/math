import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Setup
import OAI.Combinatorics.IndependentSets.PCP.ReadRelation
import OAI.Combinatorics.IndependentSets.PCP.Lookup
import OAI.Combinatorics.IndependentSets.PCP.CompareLoop
import OAI.Combinatorics.IndependentSets.PCP.EmitRows
import OAI.Combinatorics.IndependentSets.PCP.Cleanup

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open IndependentSetsGames.Foundations.Complexity
open IndependentSetsGames.Foundations.Hastad
open RuntimeModel

def headerPlan (q : Nat) := EmitRows.headerCommands q (Ambient q)
def rowPlan (q : Nat) := EmitRows.blockCommandsIn q (@context q)

inductive Label (q : Nat)
  | setup (label : Setup.Label)
  | header (label : Emitter.Label (headerPlan q).length (Addresses.fieldBound q))
  | guard | tailStart | tailLoop | reverseStart | reverseLoop | readPredicate
  | headCopyFirst | headCopySecond | indexCopyFirst | indexCopySecond
  | headVertices | headDarts | headLookup (label : Lookup.Label)
  | compare (label : CompareLoop.Label)
  | emit (label : Emitter.Label (rowPlan q).length (Addresses.fieldBound q))
  | clearField (slot : Fin 3)
  | increment | reverseOutput | cleanup (slot : Fin 16)
  deriving DecidableEq, Fintype

def headerEntry (q : Nat) : Label q :=
  .header (Emitter.labelAt (headerPlan q).length (Addresses.fieldBound q) 0 .entry)

def rowEntry (q : Nat) : Label q :=
  .emit (Emitter.labelAt (rowPlan q).length (Addresses.fieldBound q) 0 .entry)

def clearNext {q : Nat} (slot : Fin 3) : Label q :=
  if h : slot.val < 2 then .clearField ⟨slot.val + 1, by omega⟩ else .increment

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Driver
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

structure Ready (input : GenericGraphTables.Table q) (e : Nat)
    (base : Tape → List Bool) : Prop where
  le_darts : e ≤ input.darts
  original : base .original = inputBits input
  cursor : base .cursor = cursorBits input e
  vertices : base .vertices = encodeWord input.vertices
  darts : base .darts = encodeWord input.darts
  counter : base .counter = encodeWord (input.darts - e)
  edge : base .edge = encodeWord e
  tail : base .tail = []
  reverseIndex : base .reverseIndex = []
  head : base .head = []
  scratch : base .scratch = []
  compareLeft : base .compareLeft = []
  compareRight : base .compareRight = []
  output : base .output = []
  reversed : base .reversed = (prefixBits input e).reverse

theorem Ready.of_agree {input : GenericGraphTables.Table q} {e : Nat}
    {base next : Tape → List Bool} (ready : Ready input e base)
    (agree : ∀ tape, tape ≠ .scan → tape ≠ .indexScan → next tape = base tape) :
    Ready input e next where
  le_darts := ready.le_darts
  original := (agree .original (by decide) (by decide)).trans ready.original
  cursor := (agree .cursor (by decide) (by decide)).trans ready.cursor
  vertices := (agree .vertices (by decide) (by decide)).trans ready.vertices
  darts := (agree .darts (by decide) (by decide)).trans ready.darts
  counter := (agree .counter (by decide) (by decide)).trans ready.counter
  edge := (agree .edge (by decide) (by decide)).trans ready.edge
  tail := (agree .tail (by decide) (by decide)).trans ready.tail
  reverseIndex := (agree .reverseIndex (by decide) (by decide)).trans ready.reverseIndex
  head := (agree .head (by decide) (by decide)).trans ready.head
  scratch := (agree .scratch (by decide) (by decide)).trans ready.scratch
  compareLeft := (agree .compareLeft (by decide) (by decide)).trans ready.compareLeft
  compareRight := (agree .compareRight (by decide) (by decide)).trans ready.compareRight
  output := (agree .output (by decide) (by decide)).trans ready.output
  reversed := (agree .reversed (by decide) (by decide)).trans ready.reversed

theorem Ready.update_scan {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (word : List Bool) :
    Ready input e (Function.update base .scan word) := by
  apply ready.of_agree
  intro tape notScan _
  simp [notScan]

theorem Ready.update_indexScan {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (word : List Bool) :
    Ready input e (Function.update base .indexScan word) := by
  apply ready.of_agree
  intro tape _ notIndexScan
  simp [notIndexScan]

theorem Ready.counter_succ {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (he : e < input.darts) :
    base .counter = encodeWord (input.darts - (e + 1) + 1) := by
  rw [ready.counter]
  congr 1
  omega

theorem Ready.counter_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .counter = encodeWord 0 := by
  simpa only [Nat.sub_self] using ready.counter

theorem Ready.cursor_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .cursor = [] := ready.cursor.trans (cursorBits_full input)

theorem Ready.reversed_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .reversed = (GraphTables.tableBits (Table.build input)).reverse := by
  rw [ready.reversed, prefixBits_full]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

end OAI

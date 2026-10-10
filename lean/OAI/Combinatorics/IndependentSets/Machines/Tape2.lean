import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularTableRuntime
import OAI.Combinatorics.IndependentSets.Machines.VertexLabel
import OAI.Combinatorics.IndependentSets.Machines.MachineOverlayRows

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type} {d e : Nat}

abbrev Tape := Fin 5 ⊕ Fin 12
abbrev Ambient (A : Type) (d e : Nat) := ((A × Fin e) × MachineLazyRows.Buffer) × Fin d
abbrev State (A : Type) (d e : Nat) := Ambient A d e × Option Bool

def graphArchive : Tape := .inl 0
def graphStream : Tape := .inl 1
def scratch : Tape := .inl 2
def vertexCount : Tape := .inl 3
def dartCount : Tape := .inl 4
def expanderArchive : Tape := .inr 0
def expanderStream : Tape := .inr 1
def fuel : Tape := .inr 2
def vertex : Tape := .inr 3
def tail : Tape := .inr 4
def oldReverse : Tape := .inr 5
def relation : Tape := .inr 6
def dividedCopy : Tape := .inr 7
def quotient : Tape := .inr 8
def newReverse : Tape := .inr 9
def rowBuffer : Tape := .inr 10
def output : Tape := .inr 11

def oldTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, graphStream]

def expanderTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, expanderStream]

theorem oldTapes_injective : Function.Injective oldTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [oldTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, graphStream]

theorem expanderTapes_injective : Function.Injective expanderTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [expanderTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, expanderStream]

def clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) : State A d e :=
  MachineLazyRows.streamClean d hd (a, MachineFixedDivMod.residue e he 0)

def expanderState (A : Type) (d e : Nat) :
    MachineOverlayRows.State ((A × MachineLazyRows.Buffer) × Fin d) e ≃ State A d e where
  toFun
    | ((((a, buffer), rd), re), bit) => ((((a, re), buffer), rd), bit)
  invFun
    | ((((a, re), buffer), rd), bit) => ((((a, buffer), rd), re), bit)
  left_inv := by rintro ⟨⟨⟨⟨a, buffer⟩, rd⟩, re⟩, bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨a, re⟩, buffer⟩, rd⟩, bit⟩; rfl

theorem expanderState_clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) :
    expanderState A d e (MachinePortReindex.clean e he
      ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0)) =
      clean d e hd he a := rfl

inductive MainLabel (d e : Nat)
  | copyHFirst | copyHSecond
  | countSeed | countScan | countRestore
  | headerSeed | headerScan | headerRestore
  | fuelSeed | fuelScan | fuelRestore | vertexSeed | guard
  | old (stage : MachineLazyRows.VertexLabel d)
  | tailSeed | tailScan | tailRestore
  | expander (stage : MachineOverlayRows.VertexLabel e)
  | drainTail | increment
  | drainFuel | drainVertex | drainVertexCount | drainDartCount
  deriving DecidableEq, Fintype

abbrev Label (d e : Nat) := MachineTableSplit.Label ⊕ MainLabel d e

def next (l : MainLabel d e) : Option (Label d e) := some (.inr l)

def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState A d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

theorem program_main (d e : Nat) (hd : 0 < d) (he : 0 < e) (l : MainLabel d e) :
    program (A := A) d e hd he (.inr l) = mainInstruction d e hd he l := rfl

def extraTapes (rawH : List Bool) : Fin 12 → List Bool :=
  fun i => if i = 0 then rawH else []

def splitView : Tape → Option (Fin 5)
  | .inl i => some i
  | .inr _ => none

def combine (left : Fin 5 → List Bool) (rawH : List Bool) : Tape → List Bool
  | .inl i => left i
  | .inr i => extraTapes rawH i

def initialTapes (graph rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.initialTapes graph) rawH

def splitTapes (n m : Nat) (rows rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.resultTapes n m rows) rawH

theorem placedTapes (left : Fin 5 → List Bool) (rawH : List Bool) :
    Placement.tapes splitView left (initialTapes [] rawH) = combine left rawH := by
  funext k
  cases k <;> rfl

theorem splitTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (table : GraphTables.Table) (rawH : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps
      table.vertices table.darts (MachineTableSplit.rowsBits table)]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (GraphTables.tableBits table) rawH⟩) =
      some ⟨next .copyHFirst, clean d e hd he a,
        splitTapes table.vertices table.darts (MachineTableSplit.rowsBits table) rawH⟩ := by
  let ambient := (clean d e hd he a).1
  have source := MachineTableSplit.tableTrace table ambient none
  have placed := Placement.trace (Sum.inl : Fin 5 → Tape) splitView (fun _ => rfl)
    (by intro j k h; cases j <;> simp_all [splitView])
    (Sum.inl : MachineTableSplit.Label → Label d e) (next .copyHFirst)
    (initialTapes [] rawH) MachineTableSplit.program (program d e hd he) (fun _ => rfl)
    _ _ _ source
  simp only [Placement.configuration, Placement.label] at placed
  rw [placedTapes, placedTapes] at placed
  simpa only [initialTapes,
    splitTapes, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using placed

def memory (g h gs hs n m f v t out : List Bool) : Tape → List Bool
  | .inl i => ![g, gs, [], n, m] i
  | .inr i => ![h, hs, f, v, t, [], [], [], [], [], [], out] i

@[simp] theorem memory_graphArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphArchive = g := rfl
@[simp] theorem memory_graphStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphStream = gs := rfl
@[simp] theorem memory_scratch (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out scratch = [] := rfl
@[simp] theorem memory_vertexCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertexCount = n := rfl
@[simp] theorem memory_dartCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dartCount = m := rfl
@[simp] theorem memory_expanderArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderArchive = h := rfl
@[simp] theorem memory_expanderStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderStream = hs := rfl
@[simp] theorem memory_fuel (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out fuel = f := rfl
@[simp] theorem memory_vertex (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertex = v := rfl
@[simp] theorem memory_tail (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out tail = t := rfl
@[simp] theorem memory_oldReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out oldReverse = [] := rfl
@[simp] theorem memory_relation (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out relation = [] := rfl
@[simp] theorem memory_dividedCopy (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dividedCopy = [] := rfl
@[simp] theorem memory_quotient (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out quotient = [] := rfl
@[simp] theorem memory_newReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out newReverse = [] := rfl
@[simp] theorem memory_rowBuffer (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out rowBuffer = [] := rfl
@[simp] theorem memory_output (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out output = out := rfl

@[simp] theorem update_output (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) output x = memory g h gs hs n m f v t x := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_expanderStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) expanderStream x =
      memory g h gs x n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_graphStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) graphStream x =
      memory g h x hs n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_fuel (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) fuel x = memory g h gs hs n m x v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertex (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertex x = memory g h gs hs n m f x t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_tail (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) tail x = memory g h gs hs n m f v x out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertexCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertexCount x = memory g h gs hs x m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_dartCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) dartCount x = memory g h gs hs n x f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem initialTapes_memory (g h : List Bool) :
    initialTapes g h = memory g h [] [] [] [] [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [initialTapes, combine, extraTapes, MachineTableSplit.initialTapes,
      MachineTableSplit.tapes, memory]

theorem splitTapes_memory (n m : Nat) (rows rawH : List Bool) :
    splitTapes n m rows rawH = memory (encodeWords [n, m] ++ rows) rawH rows []
      (encodeWord n) (encodeWord m) [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [splitTapes, combine, extraTapes, MachineTableSplit.resultTapes,
      MachineTableSplit.tapes, memory]

def preparationSteps (n : Nat) (h : List Bool) : Nat := 2 * (h.length + 1) + 6 * (n + 1) + 4

theorem preparationTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[preparationSteps n h]
      (some ⟨next .copyHFirst, clean d e hd he a,
        memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
  let b0 := memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []
  let b1 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] []
  let b2 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] (encodeWord ((d + e) * n))
  let b3 := memory g h gs h (encodeWord n) (encodeWord m) [] [] []
    (encodeWords [n, n * (d + e)])
  let b4 := memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) [] []
    (encodeWords [n, n * (d + e)])
  let ambient := (clean d e hd he a).1
  have hcopy := MachineCopy.copyTrace expanderArchive expanderStream scratch
    (by decide) (by decide) (by decide) false (.inr .copyHFirst) (.inr .copyHSecond)
    (next .countSeed) (program d e hd he) rfl rfl b0 rfl ambient none
  have copyRun : (advance (TM2.step (program d e hd he)))^[2 * (h.length + 1)]
      (some ⟨next .copyHFirst, clean d e hd he a, b0⟩) =
      some ⟨next .countSeed, clean d e hd he a, b1⟩ := by
    simpa only [b0, b1, memory_expanderArchive, memory_expanderStream, next, List.append_nil,
      update_expanderStream, ambient, clean, MachineLazyRows.streamClean,
      MachinePortReindex.clean] using hcopy
  have hcount := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) (d + e) 0
    (.inr .countSeed) (.inr .countScan) (.inr .countRestore) (next .headerSeed)
    (program d e hd he) rfl rfl rfl b1 n [] (by simp [b1, memory, vertexCount]) rfl ambient none
  have countRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .countSeed, clean d e hd he a, b1⟩) =
      some ⟨next .headerSeed, clean d e hd he a, b2⟩ := by
    simpa only [b1, b2, memory_output, next, List.append_nil, Nat.add_zero, update_output,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hcount
  have hheader := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) 1 0
    (.inr .headerSeed) (.inr .headerScan) (.inr .headerRestore) (next .fuelSeed)
    (program d e hd he) rfl rfl rfl b2 n [] (by simp [b2, memory, vertexCount]) rfl ambient none
  have headerRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .headerSeed, clean d e hd he a, b2⟩) =
      some ⟨next .fuelSeed, clean d e hd he a, b3⟩ := by
    simpa only [b2, b3, memory_output, next, Nat.one_mul, Nat.add_zero, update_output,
      Nat.mul_comm (d + e) n, encodeWords, List.append_nil,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hheader
  have hfuel := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch fuel
    (by decide) (by decide) (by decide) 1 0
    (.inr .fuelSeed) (.inr .fuelScan) (.inr .fuelRestore) (next .vertexSeed)
    (program d e hd he) rfl rfl rfl b3 n [] (by simp [b3, memory, vertexCount]) rfl ambient none
  have fuelRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .fuelSeed, clean d e hd he a, b3⟩) =
      some ⟨next .vertexSeed, clean d e hd he a, b4⟩ := by
    simpa only [b3, b4, memory_fuel, next, List.append_nil, Nat.one_mul, Nat.add_zero,
      update_fuel, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hfuel
  have seedRun : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .vertexSeed, clean d e hd he a, b4⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .vertexSeed)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, b4, memory_vertex,
      update_vertex, next, encodeWord, List.replicate_zero, List.nil_append]
  have all := joinTrace (joinTrace (joinTrace (joinTrace copyRun countRun) headerRun) fuelRun) seedRun
  have count : preparationSteps n h =
      (((2 * (h.length + 1) + (2 * (n + 1) + 1)) + (2 * (n + 1) + 1)) +
        (2 * (n + 1) + 1)) + 1 := by unfold preparationSteps; omega
  rw [count]
  exact all

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

private theorem encodeWords_flatten (items : List (List Nat)) :
    encodeWords items.flatten = (items.map encodeWords).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatten_cons, List.map_cons, encodeWords_append, ih]

private theorem encodeWords_flatten_flatMap {α : Type*} (items : List (List α))
    (words : α → List Nat) :
    encodeWords (items.flatten.flatMap words) =
      (items.map fun xs => encodeWords (xs.flatMap words)).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.flatten_cons, List.flatMap_append, encodeWords_append, List.map_cons, ih]

def oldRows {n d : Nat} (G : PortTables.Table n d) (v : Fin n) := List.ofFn (row G v)
def expanderValues {n e : Nat} (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) : Nat :=
  (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val

def oldBlock {n d : Nat} (G : PortTables.Table n d) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsInput (oldRows G v)
def expanderBlock {n e : Nat} (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  encodeWords (List.ofFn (expanderValues H v))

def oldOutput {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsOutput d (d + e) 0 (oldRows G v)
def expanderOutput {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  MachineOverlayRows.streamOutput d e v.val (List.ofFn (expanderValues H v))
def outputBlock {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) : List Bool := oldOutput G e v ++ expanderOutput d H v

theorem oldOutput_eq {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    oldOutput G e v = encodeWords ((List.ofFn (oldRow G e v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [oldOutput, oldRows, MachineLazyRows.recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change MachineLazyRows.reindexRowBits d (d + e) 0 (row G v p).tail.val
    (row G v p).reverseIndex.val (row G v p).relation = encodeWords (rowWords (oldRow G e v p))
  rw [oldRow_words]
  simp only [MachineLazyRows.reindexRowBits, MachinePortReindex.value, Nat.add_zero,
    oldReverseMap, row, PreprocessingLazyWords.row, List.cons_append, List.nil_append,
    encodeWords, List.append_assoc]

theorem expanderOutput_eq {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) :
    expanderOutput d H v = encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) :=
  MachineOverlayRows.streamOutput_expanderRows d H v

theorem outputBlock_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputBlock G H v = encodeWords ((vertexRows G H v).flatMap rowWords) := by
  rw [outputBlock, oldOutput_eq, expanderOutput_eq]
  simp only [vertexRows, List.flatMap_append, encodeWords_append]

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

theorem expanderRows_blocks {n e : Nat} (H : ExpanderTables.Table n e) :
    encodeWords (ExpanderTableWords.rotationWords H) = (List.ofFn (expanderBlock H)).flatten := by
  rw [rotationWords_vertices, encodeWords_flatten, List.map_ofFn]
  rfl

theorem tableBits_blocks {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.tableBits (PreprocessingOverlayTables.overlay G H) =
      encodeWords [n, n * (d + e)] ++ (List.ofFn (outputBlock G H)).flatten := by
  rw [tableBits_overlay, encodeWords_append, encodeWords_flatten_flatMap, List.map_ofFn]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (outputBlock_eq G H v).symm

end IndependentSetsGames.Foundations.Complexity.MachineOverlayTable

end OAI

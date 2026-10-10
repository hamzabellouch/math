import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryAffine
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudPrefix
import OAI.Combinatorics.IndependentSets.Machines.MachinePreservingLookupClean

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open IndependentSetsGames.Foundations.PCP

namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

instance : Fintype Extra where
  elems := {.m, .index, .work, .scratch, .vertices, .darts, .emit, .output}
  complete value := by cases value <;> simp

abbrev Tape := MachineCloudPrefix.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := MachineCloudPrefix.State σ

def tableTape : Tape := .inl (.inner .table)
def nTape : Tape := .inl .bound
def queryTape : Tape := .inl (.inner .query)
def fuelTape : Tape := .inl .remaining
def sumTape : Tape := .inl .total
def mTape : Tape := .inr .m
def indexTape : Tape := .inr .index
def workTape : Tape := .inr .work
def scratchTape : Tape := .inr .scratch
def verticesTape : Tape := .inr .vertices
def dartsTape : Tape := .inr .darts
def emitTape : Tape := .inr .emit
def outputTape : Tape := .inr .output

def memory (inner : MachineCloudPrefix.Tape → List Bool)
    (m index work scratch vertices darts emit output : List Bool) : Tape → List Bool
  | .inl k => inner k
  | .inr .m => m
  | .inr .index => index
  | .inr .work => work
  | .inr .scratch => scratch
  | .inr .vertices => vertices
  | .inr .darts => darts
  | .inr .emit => emit
  | .inr .output => output

def frame (t n v f s m i w a N R e o : List Bool) : Tape → List Bool :=
  memory (MachineCloudPrefix.frame t v [] [] [] n f s) m i w a N R e o

@[simp] theorem frame_table (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o tableTape = t := rfl
@[simp] theorem frame_n (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o nTape = n := rfl
@[simp] theorem frame_query (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o queryTape = v := rfl
@[simp] theorem frame_fuel (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o fuelTape = f := rfl
@[simp] theorem frame_sum (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o sumTape = s := rfl
@[simp] theorem frame_m (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o mTape = m := rfl
@[simp] theorem frame_index (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o indexTape = i := rfl
@[simp] theorem frame_work (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o workTape = w := rfl
@[simp] theorem frame_scratch (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o scratchTape = a := rfl
@[simp] theorem frame_vertices (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o verticesTape = N := rfl
@[simp] theorem frame_darts (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o dartsTape = R := rfl
@[simp] theorem frame_emit (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o emitTape = e := rfl
@[simp] theorem frame_output (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o outputTape = o := rfl

@[simp] theorem update_frame_table (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) tableTape x =
      frame x n v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_n (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) nTape x =
      frame t x v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_query (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) queryTape x =
      frame t n x f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_fuel (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) fuelTape x =
      frame t n v x s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_sum (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) sumTape x =
      frame t n v f x m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_m (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) mTape x =
      frame t n v f s x i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_index (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) indexTape x =
      frame t n v f s m x w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_work (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) workTape x =
      frame t n v f s m i x a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_scratch (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) scratchTape x =
      frame t n v f s m i w x N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_vertices (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) verticesTape x =
      frame t n v f s m i w a x R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_darts (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) dartsTape x =
      frame t n v f s m i w a N x e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_emit (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) emitTape x =
      frame t n v f s m i w a N R x o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_output (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) outputTape x =
      frame t n v f s m i w a N R e x := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

inductive Field
  | vertices | darts
  deriving DecidableEq

instance : Fintype Field where
  elems := {.vertices, .darts}
  complete value := by cases value <;> simp

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

instance : Fintype CopyPhase where
  elems := {.count, .rEmit, .nEmit}
  complete value := by cases value <;> simp

inductive Label
  | init | seedM | clearIndex
  | lookup (field : Field) (label : MachinePreservingLookupClean.Label)
  | prefix (label : MachineCloudPrefix.Label)
  | copyFirst (phase : CopyPhase) | copySecond (phase : CopyPhase)
  | add | scaleSeed | scaleScan | scaleRestore
  | appendFirst | appendSecond | appendThird
  | cleanupZeros | clearQuery | done
  deriving DecidableEq, Fintype

def fieldTape : Field → Tape
  | .vertices => nTape
  | .darts => mTape

def fieldExit : Field → Label
  | .vertices => .seedM
  | .darts => .clearIndex

def lookupSlots (field : Field) : Fin 5 → Tape :=
  ![tableTape, indexTape, workTape, fieldTape field, scratchTape]

theorem lookupSlots_injective (field : Field) : Function.Injective (lookupSlots field) := by
  intro i j h
  cases field <;> fin_cases i <;> fin_cases j <;>
    simp_all [lookupSlots, fieldTape, tableTape, indexTape, workTape, nTape, mTape, scratchTape]

def copySource : CopyPhase → Tape
  | .count => mTape
  | .rEmit => dartsTape
  | .nEmit => verticesTape

def copyDestination : CopyPhase → Tape
  | .count => verticesTape
  | .rEmit | .nEmit => emitTape

def copyExit : CopyPhase → Label
  | .count => .add
  | .rEmit => .copyFirst .nEmit
  | .nEmit => .appendFirst

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl k => some k
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (.inl k) = some k := rfl

theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : Sum.inl k = j := by
  cases j <;> simp_all [prefixView]

theorem prefixTapes (inner : MachineCloudPrefix.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes prefixView inner extra =
      memory inner (extra mTape) (extra indexTape) (extra workTape) (extra scratchTape)
        (extra verticesTape) (extra dartsTape) (extra emitTape) (extra outputTape) := by
  funext j
  cases j with
  | inl k => rfl
  | inr k => cases k <;> rfl

variable {σ : Type}

def program (q : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push indexTape (fun _ => false) (.goto fun _ => .lookup .vertices (.run .copyFirst))
  | .seedM => .push indexTape (fun _ => true) (.goto fun _ => .lookup .darts (.run .copyFirst))
  | .clearIndex => .pop indexTape (fun state _ => (state.1, none))
      (.goto fun _ => .prefix .init)
  | .lookup field l => MachinePreservingLookupClean.statement (lookupSlots field)
      (Label.lookup field) (some (fieldExit field)) l
  | .prefix l => MachineCloudPadding.Placement.statement Sum.inl Label.prefix
      (some (.copyFirst .count)) (MachineCloudPrefix.program l)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratchTape
      id false (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratchTape (copySource phase) (copyDestination phase)
      false (.copySecond phase) (some (copyExit phase))
  | .add => MachineUnaryAddAt.loop sumTape verticesTape .add (some .scaleSeed)
  | .scaleSeed => MachineUnaryAffineAt.seed dartsTape 0 .scaleScan
  | .scaleScan => MachineUnaryAffineAt.scan verticesTape scratchTape dartsTape (q + 1)
      .scaleScan .scaleRestore
  | .scaleRestore => Reduction.MachineTransfer.loopAt scratchTape verticesTape id false
      .scaleRestore (some (.copyFirst .rEmit))
  | .appendFirst => Reduction.MachineTransfer.loopAt outputTape scratchTape id false
      .appendFirst (some .appendSecond)
  | .appendSecond => Reduction.MachineTransfer.loopAt emitTape scratchTape id false
      .appendSecond (some .appendThird)
  | .appendThird => Reduction.MachineTransfer.loopAt scratchTape outputTape id false
      .appendThird (some .cleanupZeros)
  | .cleanupZeros => .pop sumTape (fun state _ => (state.1, none))
      (.pop fuelTape (fun state _ => (state.1, none)) (.goto fun _ => .clearQuery))
  | .clearQuery => MachineLookup.discard queryTape .clearQuery .done
  | .done => .halt

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

def paddingTotal (t : GraphTables.Table) : Nat :=
  PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices

def vertexTotal (t : GraphTables.Table) : Nat :=
  PreprocessingRegularTables.vertexCount t (PreprocessingRegularTables.padding t)

def dartTotal (q : Nat) (t : GraphTables.Table) : Nat := vertexTotal t * (q + 1)

theorem vertexTotal_eq (t : GraphTables.Table) :
    vertexTotal t = t.darts + paddingTotal t := by
  unfold vertexTotal PreprocessingRegularTables.vertexCount paddingTotal
  rw [PreprocessingPaddingOffsets.offset_all]

theorem initStep (q : Nat) (table output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .init, ((ambient, false), register),
        frame table [] [] [] [] [] [] [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame table [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem seedMStep (q : Nat) (table n output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .seedM, ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 1) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem clearIndexStep (q : Nat) (table n m output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .clearIndex, ((ambient, false), register),
        frame table n [] [] [] m (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame table n [] [] [] m [] [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def readTime (t : GraphTables.Table) : Nat :=
  1 + MachinePreservingLookupClean.steps (GraphTables.tableWords t) 0 + 1 +
    MachinePreservingLookupClean.steps (GraphTables.tableWords t) 1 + 1

theorem readTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[readTime t]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ := by
  have hi : (advance (TM2.step (program q)))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ :=
    initStep q _ _ ambient register
  have hn := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .vertices)
    (lookupSlots_injective .vertices) (Label.lookup .vertices) (some Label.seedM)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 0 t.vertices (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) register
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hn
  have hs : (advance (TM2.step (program q)))^[1]
      (some ⟨some .seedM, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 1) [] [] [] [] [] output⟩ :=
    seedMStep q _ _ _ ambient none
  have hm := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .darts)
    (lookupSlots_injective .darts) (Label.lookup .darts) (some Label.clearIndex)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
      (encodeWord 1) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 1 t.darts (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) none
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hm
  have hc : (advance (TM2.step (program q)))^[1]
      (some ⟨some .clearIndex, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ :=
    clearIndexStep q _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hi hn) hs) hm) hc

end Header
end IndependentSetsGames.Foundations.Complexity.MachineRegularTable

end OAI

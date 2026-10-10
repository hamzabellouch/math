import Mathlib
import OAI.Computability.MaxCut.Machines.MachineRegularOwnerProgram

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.m, .index, .work, .scratch, .vertices,
  .darts, .emit, .output]

protected theorem Extra.enumList_getElem?_ctorIdx_eq (x : Extra) :
    Extra.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

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

protected abbrev Field.enumList : List Field := [.vertices, .darts]

protected theorem Field.enumList_getElem?_ctorIdx_eq (x : Field) :
    Field.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.count, .rEmit, .nEmit]

protected theorem CopyPhase.enumList_getElem?_ctorIdx_eq (x : CopyPhase) :
    CopyPhase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

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

private theorem appendTrace_inline_MachineRegularTable {α : Type} (f : α → α) {a b : Nat} {x y z : α}
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

/-- Both original header numbers are produced by physical preserving lookups. -/
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
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hi hn) hs) hm) hc

/-- The original vertex count is the physical bound supplied to the checked
padding-prefix machine. Its complement tapes preserve the original dart count. -/
theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

def computeTime (t : GraphTables.Table) : Nat :=
  (2 * (t.darts + 2) + (paddingTotal t + 1)) + (2 * (vertexTotal t + 1) + 1)

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hc ha) hm

def headerBits (q : Nat) (t : GraphTables.Table) : List Bool :=
  encodeWords [vertexTotal t, dartTotal q t]

theorem headerBits_eq (q : Nat) (t : GraphTables.Table) :
    headerBits q t = encodeWord (vertexTotal t) ++ encodeWord (dartTotal q t) := by
  simp only [headerBits, encodeWords, List.append_nil]

theorem headerBits_length (q : Nat) (t : GraphTables.Table) :
    (headerBits q t).length = vertexTotal t + dartTotal q t + 2 := by
  rw [headerBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def emitTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  (((2 * (dartTotal q t + 2) + 2 * (vertexTotal t + 2)) +
    (2 * ((headerBits q t).length + output.length) + 3)) + 1) + (t.vertices + 1) + 1

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hr hn) ha) hz) hc) hd

def totalTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  ((readTime t + MachineCloudPrefix.totalTime t t.vertices []) + computeTime t) + emitTime q t output

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

noncomputable def arithmeticPolynomial (q : Nat) : Polynomial Nat :=
  let X : Polynomial Nat := Polynomial.X
  let G : Polynomial Nat := Polynomial.C ExpanderFamily.growth * X
  let D : Polynomial Nat := Polynomial.C (ExpanderFamily.growth * (q + 1)) * X
  (12 * X + 11) + ((2 * (X + 2) + (G + 1)) + (2 * (G + 1) + 1)) +
    (((2 * (D + 2) + 2 * (G + 2)) + (2 * ((G + D + 2) + X) + 3)) + 1 + (X + 1) + 1)

noncomputable def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineCloudPrefix.timePolynomial.comp (2 * Polynomial.X + 1) + arithmeticPolynomial q

theorem totalTime_le (q : Nat) (t : GraphTables.Table) (output : List Bool) :
    totalTime q t output ≤ (timePolynomial q).eval ((GraphTables.tableBits t).length + output.length) := by
  let L := (GraphTables.tableBits t).length + output.length
  have hT : (GraphTables.tableBits t).length ≤ L := by unfold L; omega
  have hO : output.length ≤ L := by unfold L; omega
  have hn := (GraphTables.vertices_le_tableBits_length t).trans hT
  have hm := (GraphTables.darts_le_tableBits_length t).trans hT
  have hN : vertexTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.regularVertices_le_input t).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hS : paddingTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.prefix_le_input t t.vertices).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hR : dartTotal q t ≤ (ExpanderFamily.growth * (q + 1)) * L := by
    calc
      _ ≤ (ExpanderFamily.growth * L) * (q + 1) := Nat.mul_le_mul_right (q + 1) hN
      _ = _ := by ac_rfl
  have hr0 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 0 t.vertices
    (by simp [GraphTables.tableWords])
  have hr1 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 1 t.darts
    (by simp [GraphTables.tableWords])
  have hread : readTime t ≤ 12 * L + 11 := by
    change _ ≤ 6 * (GraphTables.tableBits t).length + 4 at hr0 hr1
    unfold readTime
    omega
  have hprefixInput : MachineCloudPrefix.inputLength t t.vertices [] ≤ 2 * L + 1 := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t t.vertices (Nat.le_refl _) []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hprefixInput)
  have harith : readTime t + computeTime t + emitTime q t output ≤
      (arithmeticPolynomial q).eval L := by
    simp only [arithmeticPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold computeTime emitTime
    rw [headerBits_length]
    omega
  have htotal := Nat.add_le_add hp harith
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- A genuine finite-machine execution with a cubic input-length budget. -/
def inTime (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩
      (some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩)
      ((timePolynomial q).eval ((GraphTables.tableBits t).length + output.length)) where
  steps := totalTime q t output
  evals_in_steps := trace q t output ambient register
  steps_le_m := totalTime_le q t output

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

/-- The outer loop consumes one real unary fuel bit. The zero delimiter is
consumed on exit; its temporary finite register is reset on both branches. -/
def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

theorem guard_succ (fuel : K) (body : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard fuel body exit) (ambient, register)
      (Function.update base fuel (encodeWord (n + 1))) =
      ⟨some body, (ambient, none), Function.update base fuel (encodeWord n)⟩ := by
  simp [guard, TM2.stepAux, encodeWord, List.replicate_succ]

theorem guard_zero (fuel : K) (body : Λ) (exit : Option Λ)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard fuel body exit) (ambient, register)
      (Function.update base fuel (encodeWord 0)) =
      ⟨exit, (ambient, none), Function.update base fuel []⟩ := by
  cases exit <;> simp [guard, TM2.stepAux, encodeWord]

/-- Unary successor needs one physical push and no unbounded register. -/
def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

theorem increment_step (counter : K) (next : Λ) (base : K → List Bool)
    (n : Nat) (state : σ) :
    TM2.stepAux (increment counter next) state (Function.update base counter (encodeWord n)) =
      ⟨some next, state, Function.update base counter (encodeWord (n + 1))⟩ := by
  simp [increment, TM2.stepAux, encodeWord, List.replicate_succ]

end Fuel

namespace Top

abbrev Body := MachineRegularOriginalBody.Tape
abbrev Tape := Body ⊕ (Header.Tape ⊕ Fin 4)
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

private def sumDecidableEq_inline_MachineRegularTable {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq_inline_MachineRegularTable
    (sumDecidableEq_inline_MachineRegularTable (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq_inline_MachineRegularTable (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq_inline_MachineRegularTable
          (sumDecidableEq_inline_MachineRegularTable
            (sumDecidableEq_inline_MachineRegularTable (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (sumDecidableEq_inline_MachineRegularTable
      (sumDecidableEq_inline_MachineRegularTable (inferInstanceAs (DecidableEq MachineCloudPrefix.Tape))
        (inferInstanceAs (DecidableEq Header.Extra)))
      (inferInstanceAs (DecidableEq (Fin 4))))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def coreTape (i : Fin 27) : Tape := .inl (.inl i)
def oldFuel : Tape := .inr (.inr 0)
def ownerFuel : Tape := .inr (.inr 1)
def dummyFuel : Tape := .inr (.inr 2)
def scratch : Tape := .inr (.inr 3)

def headerTape (k : Header.Tape) : Tape :=
  if k = Header.tableTape then coreTape 0
  else if k = Header.mTape then coreTape 6
  else if k = Header.outputTape then coreTape 8
  else .inr (.inl k)

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

def ownerView : Tape → Option MachineRegularOwnerBody.Tape
  | .inl k => some (.inl k)
  | .inr (.inl _) => none
  | .inr (.inr i) => match i.val with
    | 2 => some (.inr 0)
    | 3 => some (.inr 1)
    | _ => none

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

def headerStates :
    (Header.State Unit × (MachineRegularOriginalBody.CoreState ×
      (MachineRegularOriginalBody.FamilyState × Option Bool))) ≃ State where
  toFun p := (((p.2.1, p.1), p.2.2.1), p.2.2.2)
  invFun p := (p.1.1.2, (p.1.1.1, (p.1.2, p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

inductive CopyPhase | old | owner
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.old, .owner]

protected theorem CopyPhase.enumList_getElem?_ctorIdx_eq (x : CopyPhase) :
    CopyPhase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

def copySource : CopyPhase → Tape
  | .old => coreTape 6
  | .owner => headerTape Header.nTape
def copyTarget : CopyPhase → Tape
  | .old => oldFuel
  | .owner => ownerFuel

inductive Label
  | header (l : Header.Label)
  | oldSeed
  | copyFirst (phase : CopyPhase)
  | copySecond (phase : CopyPhase)
  | oldGuard
  | oldBody (l : MachineRegularOriginalBody.Label)
  | oldIncrement
  | ownerSeed
  | ownerGuard
  | ownerBody (l : MachineRegularOwnerBody.Label)
  | ownerIncrement
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

/-- All graph-dependent loop counts remain on tapes. The code contains only
the fixed expander base and the finite subprogram labels. -/
def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

/-- These are mathematical descriptions of the physical stacks at loop
boundaries. They are never loaded into the machine's finite control. -/
def frame (data : Data) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr (.inl k) => header k
  | .inr (.inr i) => counters i

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

@[simp] theorem frame_core (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (i : Fin 27) :
    frame data header counters (coreTape i) = MachineRegularMetadata.frame data (.inl i) := rfl

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

def headerAux (n N R : List Bool) : Header.Tape → List Bool := fun k =>
  if k = Header.nTape then n
  else if k = Header.verticesTape then N
  else if k = Header.dartsTape then R
  else []

@[simp] theorem headerAux_empty : headerAux [] [] [] = (fun _ => []) := by
  funext k
  simp [headerAux]

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

end Top
end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI

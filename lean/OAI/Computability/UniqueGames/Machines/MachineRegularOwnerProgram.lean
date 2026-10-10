import OAI.Computability.UniqueGames.Machines.MachineRegularOriginalBody
import OAI.Computability.UniqueGames.Machines.MachineRegularOwnerCleanup
import OAI.Computability.UniqueGames.PCP.PreprocessingRegularLoopWordsLemmas

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Data := MachineRegularMetadata.Data
abbrev CoreState := MachineRegularOriginalBody.CoreState
abbrev MetaState := MachineRegularOriginalBody.MetaState
abbrev FamilyState := MachineRegularOriginalBody.FamilyState
abbrev BaseTable := PreprocessingRegularTables.BaseTable

instance : DecidableEq Tape := MachineRegularOwnerCleanup.tapeDecidableEq
instance : Fintype Tape := MachineRegularOwnerCleanup.tapeFintype

def core (k : Fin 27) : Tape := .inl (.inl k)
def paddingTape : Tape := .inl (.inr (.inl .padding))
def levelTape : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def metadataTape (k : MachineRegularMetadata.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.metadataTape k)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl k => MachineRegularOriginalBody.metadataView k
  | .inr _ => none

def familyTape (k : MachineRegularFamily.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.familyTape k)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl k => MachineRegularOriginalBody.familyView k
  | .inr _ => none

def vertexView : Tape → Option (Fin 27)
  | .inl k => MachineRegularOriginalBody.vertexView k
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := MachineRegularOriginalBody.metadataView_left k

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.metadataView_right j k h)
  | inr j => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := MachineRegularOriginalBody.familyView_left k

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.familyView_right j k h)
  | inr j => cases h

theorem vertexView_left (k : Fin 27) : vertexView (core k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : core k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.vertexView_right j k h)
  | inr j => cases h

def metadataStates : (MetaState × ((CoreState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.2.1.1, p.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.2, ((p.1.1.1, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × ((CoreState × MetaState) × Option Bool)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def vertexStates : (CoreState × ((MetaState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | copyCount (l : MachineUnaryAffineAt.Label)
  | copyFuel (l : MachineUnaryAffineAt.Label)
  | guard
  | family (l : MachineRegularFamily.Label)
  | loop
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | bump
  | cleanup (l : MachineRegularOwnerCleanup.Label)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.cloud .init)

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.copyCount .seed))
      metadataStates (MachineRegularMetadata.program l)
  | .copyCount .seed => MachineUnaryAffineAt.seed (core 3) 0 (.copyCount .scan)
  | .copyCount .scan => MachineUnaryAffineAt.scan (core 4) scratch (core 3) 1
      (.copyCount .scan) (.copyCount .restore)
  | .copyCount .restore => Reduction.MachineTransfer.loopAt scratch (core 4) id false
      (.copyCount .restore) (some (.copyFuel .seed))
  | .copyFuel .seed => MachineUnaryAffineAt.seed dummyFuel 0 (.copyFuel .scan)
  | .copyFuel .scan => MachineUnaryAffineAt.scan paddingTape scratch dummyFuel 1
      (.copyFuel .scan) (.copyFuel .restore)
  | .copyFuel .restore => Reduction.MachineTransfer.loopAt scratch paddingTape id false
      (.copyFuel .restore) (some .guard)
  | .guard => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .family .start))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .family l => Lift.statement familyTape Label.family (some .loop)
      familyStates (MachineRegularFamily.program H l)
  | .loop => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop dummyFuel (fun state _ => (state.1, none))
          (.goto fun _ => .vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .vertex l => Lift.statement core Label.vertex (some .bump)
      vertexStates (MachineRegularOriginalBody.vertexSource l)
  | .bump => .push (core 1) (fun _ => true)
      (.push (core 3) (fun _ => true) (.goto fun _ => .loop))
  | .cleanup l => MachineRegularOwnerCleanup.instruction Label.cleanup none l

def working (data : Data) (fuel saved : List Bool) : Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr i => if i = 0 then fuel else saved

def frame (data : Data) : Tape → List Bool := working data [] []

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val)
  owner := encodeWord v.val
  localRank := []
  count := []
  offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val)
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  MachineRegularMetadata.cloudData t v (initialData t v output)

def seededData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  { metadataData t v output with localRank := encodeWord (cloudSize t v) }

def ownerBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) : List Bool :=
  (List.ofFn (PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v)).flatten

def finalData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Data :=
  { initialData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    output := output ++ ownerBits H t v }

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI

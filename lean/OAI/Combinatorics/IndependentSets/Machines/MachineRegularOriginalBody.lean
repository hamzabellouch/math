import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularLift
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularMetadata
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularFamily
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularVertexBlock
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingFamilyBridge

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev CoreState := MachineRegularInternalRow.CoreState Unit internalDegree
abbrev MetaState := MachineRegularMetadata.State Unit
abbrev FamilyState := MachineRegularFamily.State
abbrev State := (CoreState × MetaState) × FamilyState
abbrev Data := MachineRegularMetadata.Data
abbrev BaseTable := PreprocessingRegularTables.BaseTable

theorem degree_positive : 0 < internalDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def readyState (H : BaseTable) : State :=
  ((MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
    (((), false), none)), MachineRegularFamily.readyState H)

def metadataTape : MachineRegularMetadata.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inl e)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl i => some (.inl i)
  | .inr (.inl e) => some (.inr e)
  | .inr (.inr _) => none

def familyTape : MachineRegularFamily.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inr e)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl i => some (.inl i)
  | .inr (.inl _) => none
  | .inr (.inr e) => some (.inr e)

def vertexView : Tape → Option (Fin 27)
  | .inl i => some i
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := by cases k <;> rfl

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h; rfl
    | inr e => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := by cases k <;> rfl

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h
    | inr e => cases h; rfl

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : Sum.inl k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr e => cases h

def metadataStates : (MetaState × (CoreState × FamilyState)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × (CoreState × MetaState)) ≃ State := Equiv.prodComm _ _
def vertexStates : (CoreState × (MetaState × FamilyState)) ≃ State :=
  (Equiv.prodAssoc _ _ _).symm

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | family (l : MachineRegularFamily.Label)
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.owner .seed)

def clearTape : Fin 7 → Tape :=
  ![.inl 2, .inl 3, .inl 4, .inl 5, .inl 7,
    .inr (.inl .padding), .inr (.inl .level)]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

def clearSource (source : Tape) : Unit → TM2.Stmt Alphabet Unit MetaState :=
  fun _ => MachineDrain.drain source () none

def vertexSource : MachineRegularVertexBlock.Label internalDegree →
    TM2.Stmt (fun _ : Fin 27 => Bool) (MachineRegularVertexBlock.Label internalDegree) CoreState :=
  MachineRegularVertexBlock.instruction internalDegree degree_positive id none

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.family .start))
      metadataStates (MachineRegularMetadata.program l)
  | .family l => Lift.statement familyTape Label.family
      (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
      familyStates (MachineRegularFamily.program H l)
  | .vertex l => Lift.statement Sum.inl Label.vertex (clearEntry 0)
      vertexStates (vertexSource l)
  | .clear i => Lift.statement id (fun _ : Unit => .clear i) (clearEntry (i.val + 1))
      metadataStates (clearSource (clearTape i) ())

def frame (data : Data) : Tape → List Bool
  | .inl i => MachineRegularMetadata.frame data (.inl i)
  | .inr (.inl e) => MachineRegularMetadata.frame data (.inr e)
  | .inr (.inr _) => []

def coreFrame (data : Data) (i : Fin 27) : List Bool :=
  MachineRegularMetadata.frame data (.inl i)

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord e.val
  owner := []
  localRank := []
  count := []
  offset := []
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data :=
  MachineRegularMetadata.originalData t e (initialData t e output)

def familyData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { metadataData t e output with
    rotor := MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) }

def emittedBits (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  PreprocessingRegularWords.originalVertexBits t (padding t) (familyCloudTable H t) e

def emittedData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { familyData H t e output with output := output ++ emittedBits H t e }

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem familyPlacement (data : Data) :
    MachineCloudPadding.Placement.tapes familyView (MachineRegularFamily.frame (coreFrame data))
      (frame data) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k (coreFrame data)))
      (frame data) = frame { data with rotor := MachineRegularFamily.rotor H k } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [MachineCloudPadding.Placement.tapes, familyView, MachineRegularFamily.frame,
        MachineRegularFamily.resultCore, coreFrame, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t t.rows[e].tail)
    (coreFrame (metadataData t e output)) rfl rfl (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) : Nat :=
  (familyExecution H t e output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

def clearMemory (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k + 1 => if h : k < 7 then
      Function.update (clearMemory base k) (clearTape ⟨k, h⟩) [] else clearMemory base k

def clearSteps (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => clearSteps base k + if h : k < 7 then
      ((clearMemory base k) (clearTape ⟨k, h⟩)).length + 1 else 0

private theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

theorem clearFrame (data : Data) : clearMemory (frame data) 7 =
    frame { data with
      owner := []
      localRank := []
      count := []
      offset := []
      rotor := []
      padding := []
      level := [] } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;>
        simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
    | inr e => simp [clearMemory, clearTape, frame]

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    coreFrame (familyData H t e output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        t.rows[e].tail (MachineRegularVertexBlock.oldCloud t (padding t) e) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t t.rows[e].tail)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t t.rows[e].tail
      (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  funext i
  fin_cases i <;>
    simp [coreFrame, familyData, metadataData, MachineRegularMetadata.originalData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
      MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData,
      MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      MachineRegularVertexBlock.oldCloud, paddedOld,
      MachineRegularMetadata.originalMember]
  all_goals first | exact rotor | rfl

theorem emittedData_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : emittedData H t e output =
      familyData H t e (output ++ emittedBits H t e) := rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output output' : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView (coreFrame (familyData H t e output'))
      (frame (familyData H t e output)) = frame (familyData H t e output') := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

def vertexSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularVertexBlock.originalSteps t (padding t) (familyCloudTable H t) e output.length

theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularMetadata.totalTime t e + familySteps H t e output + vertexSteps H t e output +
    clearSteps (frame (emittedData H t e output)) 7

theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace (joinTrace (joinTrace metadata family) vertex) cleanup

noncomputable def originalExecution (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t e output))
      (some (cfg H none (initialData t e (output ++ emittedBits H t e))))
      (totalSteps H t e output) where
  steps := totalSteps H t e output
  evals_in_steps := originalTrace H t e output
  steps_le_m := le_rfl

end IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI

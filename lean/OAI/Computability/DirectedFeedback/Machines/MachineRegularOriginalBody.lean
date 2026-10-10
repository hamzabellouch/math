import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.PreprocessingRegularWords

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open DFVSGames.Foundations.Complexity (encodeWords)

theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

theorem familyRotor_eq_familyCloudTable (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : 0 < cloudSize t v) :
    encodeWords (rotationWords (ExpanderTables.family H
      (PreprocessingLevels.boundedLevel (cloudSize t v)))) =
      encodeWords (rotationWords (familyCloudTable H t v)) := by
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  exact congrArg encodeWords (rotationWords_resizeTable _ _).symm

theorem cloudSize_pos_of_dart (t : GraphTables.Table) (e : Fin t.darts) :
    0 < cloudSize t t.rows[e].tail := by
  have h := (oldCloudIndex t e).isLt
  omega

theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

theorem cloudSize_pos_of_paddedCloud (t : GraphTables.Table) (v : Fin t.vertices)
    (x : PaddedCloud t (padding t) v) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hx := (paddedCloudRank t (padding t) v x).isLt
  omega

theorem familyCloudWords_of_zero (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : cloudSize t v = 0) :
    encodeWords (rotationWords (familyCloudTable H t v)) = [] := by
  have hl : (rotationWords (familyCloudTable H t v)).length = 0 := by
    rw [rotationWords_length, cloudSize_add_padding, hk,
      PreprocessingLevels.cloudPaddedSize_zero, Nat.zero_mul]
  rw [List.length_eq_zero_iff.mp hl]
  rfl

end DFVSGames.Foundations.PCP.PreprocessingFamilyBridge
end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOriginalBody

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

private theorem joinTrace_inline_MachineRegularOriginalBody {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
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

private theorem identityPlacement_inline_MachineRegularOriginalBody (base extra : Tape → List Bool) :
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
    identityPlacement_inline_MachineRegularOriginalBody, metadataStates, Equiv.coe_fn_mk, readyState] using placed

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
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace_inline_MachineRegularOriginalBody first second

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
  exact joinTrace_inline_MachineRegularOriginalBody (joinTrace_inline_MachineRegularOriginalBody (joinTrace_inline_MachineRegularOriginalBody metadata family) vertex) cleanup

noncomputable def originalExecution (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t e output))
      (some (cfg H none (initialData t e (output ++ emittedBits H t e))))
      (totalSteps H t e output) where
  steps := totalSteps H t e output
  evals_in_steps := originalTrace H t e output
  steps_le_m := le_rfl

end DFVSGames.Foundations.Complexity.MachineRegularOriginalBody
end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {LabelType : Type}

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Alphabet (_ : Tape) := Bool

private def sumDecidableEq_inline_MachineRegularOwnerCleanup {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
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
  sumDecidableEq_inline_MachineRegularOwnerCleanup
    (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq_inline_MachineRegularOwnerCleanup
          (sumDecidableEq_inline_MachineRegularOwnerCleanup
            (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

def cleanupEntry (labels : Label → LabelType) (exit : Option LabelType) : Option LabelType :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

def instruction (labels : Label → LabelType) (exit : Option LabelType) :
    Label → TM2.Stmt Alphabet LabelType State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

theorem finalTapes_empty (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∈ cleanupTapes) : finalTapes base d o k = [] := by
  rw [finalTapes_apply, ite_eq_left hk]

theorem finalTapes_other (base : Tape → List Bool) (d o : Nat) (k : Tape)
    (hk : k ∉ cleanupTapes) (hp : k ≠ prefixTape) :
    finalTapes base d o k = base k := by
  rw [finalTapes_apply, ite_eq_right hk, ite_eq_right hp]

@[simp] theorem finalTapes_scratch (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o scratch = base scratch := by
  apply finalTapes_other
  · simp [cleanupTapes, scratch, localRank, count, rotor, padding, level, dummyFuel, core]
  · decide

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

theorem additionTraceAt (labels : Label → LabelType) (exit : Option LabelType)
    (program : LabelType → TM2.Stmt Alphabet LabelType State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

theorem traceAt (labels : Label → LabelType) (exit : Option LabelType)
    (program : LabelType → TM2.Stmt Alphabet LabelType State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second

def executionAt (labels : Label → LabelType) (exit : Option LabelType)
    (program : LabelType → TM2.Stmt Alphabet LabelType State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels entry), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), finalTapes base d o⟩) (steps base d) where
  steps := steps base d
  evals_in_steps := traceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup
end

section

namespace DFVSGames.Foundations.PCP.PreprocessingRegularLoopWords

def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksSuffix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksSuffix f k = f ⟨k, h⟩ ++ blocksSuffix f (k + 1) := by
  unfold blocksSuffix
  rw [List.drop_eq_getElem_cons
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_cons, List.getElem_ofFn]

theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end DFVSGames.Foundations.PCP.PreprocessingRegularLoopWords

end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerBody

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

end DFVSGames.Foundations.Complexity.MachineRegularOwnerBody
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

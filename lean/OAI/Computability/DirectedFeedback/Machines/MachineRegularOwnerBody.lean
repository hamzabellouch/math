import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineRegularOriginalBody

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

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

private theorem joinTrace_inline_MachineRegularOwnerBody {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem oneStep_inline_MachineRegularOwnerBody {A : Type} {f : A → Option A} {a b : A}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j <;> rfl
  | inr i => rfl

theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineCloudPadding.totalTime t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H (some (.copyCount .seed)) (metadataData t v output)) := by
  have raw := MachineRegularMetadata.cloudTrace t v (initialData t v output)
    rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.copyCount .seed)) metadataStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), MachineRegularFamily.readyState H), none)
    (frame (initialData t v output)) MachineRegularMetadata.program (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    MachineRegularOriginalBody.readyState, metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem working_update_local (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 3) word =
      working { data with localRank := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

theorem working_update_fuel (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) dummyFuel word = working data word saved := by
  funext j
  cases j with
  | inl j => simp [working, dummyFuel]
  | inr i => fin_cases i <;> simp [working, dummyFuel]

theorem working_update_global (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 1) word =
      working { data with globalIndex := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

theorem working_update_output (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 8) word =
      working { data with output := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

theorem copyCountTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (cloudSize t v + 1) + 1]
      (some (cfg H (some (.copyCount .seed)) (metadataData t v output))) =
      some (cfg H (some (.copyFuel .seed)) (seededData t v output)) := by
  have run := MachineUnaryAffineAt.seededAffineTrace (core 4) scratch (core 3)
    (by decide) (by decide) (by decide) 1 0
    (.copyCount .seed) (.copyCount .scan) (.copyCount .restore) (some (.copyFuel .seed))
    (program H) rfl rfl rfl (frame (metadataData t v output)) (cloudSize t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (metadataData t v output) (core 3) = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_local, seededData] using run

theorem copyFuelTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (padding t v + 1) + 1]
      (some (cfg H (some (.copyFuel .seed)) (seededData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ := by
  have run := MachineUnaryAffineAt.seededAffineTrace paddingTape scratch dummyFuel
    (by decide) (by decide) (by decide) 1 0
    (.copyFuel .seed) (.copyFuel .scan) (.copyFuel .restore) (some .guard)
    (program H) rfl rfl rfl (frame (seededData t v output)) (padding t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (seededData t v output) dummyFuel = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_fuel] using run

theorem guardZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by
  rfl

theorem guardPositiveStep (H : BaseTable) (data : Data) (d : Nat) (hd : 0 < d) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord d) []⟩ =
      some ⟨some (.family .start), readyState H, working data (encodeWord d) []⟩ := by
  cases d with
  | zero => omega
  | succ d =>
      simp [TM2.step, program, TM2.stepAux, working, dummyFuel, encodeWord,
        List.replicate_succ, readyState]

def dummyBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    Fin (padding t v) → List Bool :=
  PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v

def vertexData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output : List Bool) : Data :=
  { seededData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + n)
    localRank := encodeWord (cloudSize t v + n)
    rotor := MachineRegularFamily.rotor H (cloudSize t v) }

def loopData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Data :=
  vertexData H t v n (output ++ blocksPrefix (dummyBits H t v) n)

def loopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Tape → List Bool :=
  working (loopData H t v output n) (encodeWord (padding t v - n)) []

def preSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (2 * (cloudSize t v + 1) + 1) +
    (2 * (padding t v + 1) + 1)

def loopSteps (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : (n : Nat) → n ≤ padding t v → Nat
  | 0, _ => 0
  | n + 1, hn => loopSteps H t v output n (by omega) +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t)
        v ⟨n, by omega⟩ (output ++ blocksPrefix (dummyBits H t v) n).length + 1)

def cleanupCost (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  if padding t v = 0 then
    MachineRegularOwnerCleanup.steps (working (seededData t v output) (encodeWord 0) []) (padding t v)
  else MachineRegularOwnerCleanup.steps (loopFrame H t v output (padding t v)) (padding t v)

noncomputable def ownerTime (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  preSteps t v + 1 + (if padding t v = 0 then 0 else
    MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length +
      loopSteps H t v output (padding t v) le_rfl + 1) + cleanupCost H t v output

theorem familyPlacement (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularOriginalBody.coreFrame data))
      (working data fuel saved) = working data fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyPlacement data) j
  | inr i => rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k
        (MachineRegularOriginalBody.coreFrame data)))
      (working data fuel saved) =
      working { data with rotor := MachineRegularFamily.rotor H k } fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyResultPlacement H k data) j
  | inr i => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t v)
    (MachineRegularOriginalBody.coreFrame (seededData t v output)) rfl rfl
    (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat :=
  (familyExecution H t v output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t v output]
      (some ⟨some (.family .start), readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output 0⟩ := by
  have raw := (familyExecution H t v output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some .loop) familyStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), ((((), false), none) : MetaState)), none)
    (working (seededData t v output) (encodeWord (padding t v)) [])
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familySteps, readyState,
    MachineRegularOriginalBody.readyState, familyStates, Equiv.coe_fn_mk,
    loopFrame, loopData, vertexData, blocksPrefix_zero, List.append_nil, Nat.sub_zero,
    Nat.add_zero, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData] using placed

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output : List Bool) :
    MachineRegularOriginalBody.coreFrame (vertexData H t v j.val output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        v (paddedNew t (padding t) v j) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t v) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t v)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
      (PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v j)
  funext i
  fin_cases i <;>
    simp [MachineRegularOriginalBody.coreFrame, vertexData, seededData, metadataData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      paddedNew,
      PreprocessingPaddingOffsets.paddingOrder_val, Nat.add_assoc]
  all_goals first | exact rotor | rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output output' fuel : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView
      (MachineRegularOriginalBody.coreFrame (vertexData H t v n output'))
      (working (vertexData H t v n output) fuel []) =
      working (vertexData H t v n output') fuel [] := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr i => rfl

theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output fuel : List Bool) :
    (advance (TM2.step (program H)))^[
        MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j output.length]
      (some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working (vertexData H t v j.val output) fuel []⟩) =
      some ⟨some .bump, readyState H,
        working (vertexData H t v j.val (output ++ dummyBits H t v j)) fuel []⟩ := by
  have raw := MachineRegularVertexBlock.dummyTraceAt internalDegree
    MachineRegularOriginalBody.degree_positive id none MachineRegularOriginalBody.vertexSource
    (fun _ => rfl) t (padding t) (familyCloudTable H t) v j output ()
  have finished := coreFrame_eq H t v j (output ++ dummyBits H t v j)
  simp only [dummyBits] at finished
  rw [← coreFrame_eq H t v j output, ← finished] at raw
  have placed := Lift.trace core vertexView vertexView_left vertexView_right
    Label.vertex (some .bump) vertexStates
    ((((((), false), none) : MetaState), MachineRegularFamily.readyState H), none)
    (working (vertexData H t v j.val output) fuel [])
    MachineRegularOriginalBody.vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    readyState, MachineRegularOriginalBody.readyState, vertexStates, Equiv.coe_fn_mk,
    dummyBits, id_eq] using placed

@[simp] theorem working_fuel (data : Data) (fuel saved : List Bool) :
    working data fuel saved dummyFuel = fuel := rfl

@[simp] theorem working_scratch (data : Data) (fuel saved : List Bool) :
    working data fuel saved scratch = saved := rfl

theorem loopPositiveStep (H : BaseTable) (data : Data) (d : Nat) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord (d + 1)) []⟩ =
      some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working data (encodeWord d) []⟩ := by
  change some (TM2.stepAux (program H .loop) _ _) = _
  simp only [program, TM2.stepAux, working_fuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, Option.getD_some, Bool.cond_true,
    List.tail_cons, working_update_fuel]
  rfl

theorem loopZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by rfl

theorem bumpStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output fuel : List Bool) :
    TM2.step (program H) ⟨some .bump, readyState H, working (vertexData H t v n output) fuel []⟩ =
      some ⟨some .loop, readyState H, working (vertexData H t v (n + 1) output) fuel []⟩ := by
  change some (TM2.stepAux (program H .bump) _ _) = _
  simp only [program, TM2.stepAux,
    Function.update_of_ne (by decide : core 3 ≠ core 1),
    working_update_global, working_update_local]
  congr 2

theorem loopPrefixTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    (advance (TM2.step (program H)))^[loopSteps H t v output n hn]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : n < padding t v := by omega
      have first := ih (by omega)
      have hremaining : padding t v - n = (padding t v - (n + 1)) + 1 := by omega
      have guard := loopPositiveStep H (loopData H t v output n) (padding t v - (n + 1))
      rw [← hremaining] at guard
      have guardRun : (advance (TM2.step (program H)))^[1]
          (some ⟨some .loop, readyState H, loopFrame H t v output n⟩) =
          some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)), readyState H,
            working (loopData H t v output n) (encodeWord (padding t v - (n + 1))) []⟩ := oneStep_inline_MachineRegularOwnerBody guard
      have vertex := vertexTrace H t v ⟨n, h⟩
        (output ++ blocksPrefix (dummyBits H t v) n) (encodeWord (padding t v - (n + 1)))
      have bump := bumpStep H t v n
        ((output ++ blocksPrefix (dummyBits H t v) n) ++ dummyBits H t v ⟨n, h⟩)
        (encodeWord (padding t v - (n + 1)))
      have bumpRun := oneStep_inline_MachineRegularOwnerBody bump
      have all := joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody first guardRun) vertex) bumpRun
      simpa only [loopSteps, loopFrame, loopData, blocksPrefix_succ _ n h,
        List.append_assoc, Nat.add_assoc] using all

theorem preparationTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[preSteps t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
  joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (metadataTrace H t v output) (copyCountTrace H t v output))
    (copyFuelTrace H t v output)

theorem cleanupFrame (data : Data) (fuel : List Bool) (d o : Nat) :
    MachineRegularOwnerCleanup.finalTapes (working data fuel []) d o =
      frame { data with
        localRank := []
        count := []
        rotor := []
        padding := []
        level := []
        offset := encodeWord (d + o) } := by
  funext j
  rw [MachineRegularOwnerCleanup.finalTapes_apply]
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
          MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
          MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
          MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
          MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
          MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
            MachineRegularMetadata.frame]
      | inr e =>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame]
  | inr i => fin_cases i <;>
      simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
        MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
        MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
        MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
        MachineRegularOwnerCleanup.core, frame, working]

theorem ownerBits_zero (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (hp : padding t v = 0) : ownerBits H t v = [] := by
  have hnil : List.ofFn (dummyBits H t v) = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [List.length_ofFn] using hp
  exact congrArg List.flatten hnil

theorem cleanupZeroFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    MachineRegularOwnerCleanup.finalTapes
      (working (seededData t v output) (encodeWord 0) []) (padding t v)
      (PreprocessingPaddingOffsets.offset (padding t) v.val) = frame (finalData H t v output) := by
  rw [cleanupFrame]
  apply congrArg frame
  simp only [seededData, metadataData, MachineRegularMetadata.cloudData, initialData,
    finalData, hp, ownerBits_zero H t v hp, List.append_nil, Nat.add_zero, Nat.zero_add]

theorem cleanupLoopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerCleanup.finalTapes (loopFrame H t v output (padding t v))
      (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) =
        frame (finalData H t v output) := by
  rw [loopFrame, cleanupFrame]
  apply congrArg frame
  simp only [loopData, vertexData, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData, finalData, blocksPrefix_all, dummyBits, ownerBits,
    Nat.add_comm (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val)]

theorem cleanupZeroTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (working (seededData t v output) (encodeWord 0) []) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working (seededData t v output) (encodeWord 0) []⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (working (seededData t v output) (encodeWord 0) []) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupZeroFrame H t v output hp] at run
  exact run

theorem cleanupLoopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (loopFrame H t v output (padding t v)) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (loopFrame H t v output (padding t v)) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupLoopFrame] at run
  exact run

theorem loopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[loopSteps H t v output (padding t v) le_rfl + 1]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
  have first := loopPrefixTrace H t v output (padding t v) le_rfl
  have last : (advance (TM2.step (program H)))^[1]
      (some ⟨some .loop, readyState H, loopFrame H t v output (padding t v)⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
    simpa only [loopFrame, Nat.sub_self] using
      oneStep_inline_MachineRegularOwnerBody (loopZeroStep H (loopData H t v output (padding t v)))
  exact joinTrace_inline_MachineRegularOwnerBody first last

noncomputable def ownerInTime (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t v output))
      (some (cfg H none (finalData H t v output))) (ownerTime H t v output) := by
  have prepared := preparationTrace H t v output
  by_cases hp : padding t v = 0
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
          working (seededData t v output) (encodeWord 0) []⟩ := by
      simpa only [hp] using oneStep_inline_MachineRegularOwnerBody (guardZeroStep H (seededData t v output))
    have all := joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody prepared gate) (cleanupZeroTrace H t v output hp)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    simp only [ownerTime, cleanupCost, ite_eq_left hp, Nat.add_zero, le_refl]
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.family .start), readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
      oneStep_inline_MachineRegularOwnerBody (guardPositiveStep H (seededData t v output) (padding t v) (Nat.pos_of_ne_zero hp))
    have all := joinTrace_inline_MachineRegularOwnerBody
      (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody prepared gate) (familyTrace H t v output))
        (loopTrace H t v output)) (cleanupLoopTrace H t v output)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    have hb : familySteps H t v output ≤
        MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length :=
      (familyExecution H t v output).steps_le_m
    simp only [ownerTime, cleanupCost, ite_eq_right hp]
    omega

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat := (ownerInTime H t v output).steps

theorem ownerTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t v output]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H none (finalData H t v output)) := (ownerInTime H t v output).evals_in_steps

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : totalSteps H t v output ≤ ownerTime H t v output :=
  (ownerInTime H t v output).steps_le_m

end DFVSGames.Foundations.Complexity.MachineRegularOwnerBody

end

section

namespace DFVSGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open DFVSGames.Foundations.Complexity
open scoped BigOperators

def inputLength (t : GraphTables.Table) : Nat := (GraphTables.tableBits t).length

theorem cloudSize_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v ≤ inputLength t :=
  (cloudSize_le_darts t v).trans (GraphTables.darts_le_tableBits_length t)

theorem cloudTotal_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v + padding t v ≤ ExpanderFamily.growth * inputLength t := by
  rw [cloudSize_add_padding]
  exact (PreprocessingLevels.cloudPaddedSize_bounds _).2.trans
    (Nat.mul_le_mul_left _ (cloudSize_le_input t v))

theorem level_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingLevels.boundedLevel (cloudSize t v) ≤ inputLength t :=
  (PreprocessingLevels.boundedLevel_le_input _).trans (cloudSize_le_input t v)

theorem regularVertices_le_input (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * inputLength t :=
  (vertexCount_le t).trans
    (Nat.mul_le_mul_left _ (GraphTables.darts_le_tableBits_length t))

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

theorem prefix_le_input (t : GraphTables.Table) (k : Nat) :
    PreprocessingPaddingOffsets.offset (padding t) k ≤
      ExpanderFamily.growth * inputLength t := by
  have hsum : (∑ v, padding t v) ≤ vertexCount t (padding t) := by
    unfold vertexCount
    omega
  exact (offset_le_sum (padding t) k).trans (hsum.trans (regularVertices_le_input t))

noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end DFVSGames.Foundations.PCP.PreprocessingMachineBounds
end

section

namespace DFVSGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open DFVSGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem visits_le_input :
    t.darts + t.vertices + (∑ v, padding t v) + 1 ≤
      (ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1 := by
  have hv := PreprocessingMachineBounds.regularVertices_le_input t
  have hn := GraphTables.vertices_le_tableBits_length t
  change t.vertices ≤ PreprocessingMachineBounds.inputLength t at hn
  unfold vertexCount at hv
  rw [Nat.add_mul, one_mul]
  omega

theorem sum_body_costs_le (old : Fin t.darts → Nat) (owners : Fin t.vertices → Nat)
    (dummy : ∀ v : Fin t.vertices, Fin (padding t v) → Nat) (setup cap : Nat)
    (hs : setup ≤ cap) (ho : ∀ e, old e ≤ cap) (hv : ∀ v, owners v ≤ cap)
    (hd : ∀ v j, dummy v j ≤ cap) :
    setup + (∑ e, old e) + (∑ v, owners v) + (∑ v, ∑ j, dummy v j) ≤
      ((ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1) * cap := by
  have hOld : (∑ e, old e) ≤ t.darts * cap := by
    simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => ho e)
  have hOwners : (∑ v, owners v) ≤ t.vertices * cap := by
    simpa using Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hv v)
  have hDummy : (∑ v, ∑ j, dummy v j) ≤ (∑ v, padding t v) * cap := by
    calc
      _ ≤ ∑ v, padding t v * cap := by
        apply Finset.sum_le_sum
        intro v _
        simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd v j)
      _ = _ := (Finset.sum_mul ..).symm
  calc
    _ ≤ (t.darts + t.vertices + (∑ v, padding t v) + 1) * cap := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, one_mul]
      omega
    _ ≤ _ := Nat.mul_le_mul_right cap (visits_le_input t)

end DFVSGames.Foundations.PCP.PreprocessingRegularBounds
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

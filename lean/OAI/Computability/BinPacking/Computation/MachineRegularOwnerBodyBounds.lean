import OAI.Computability.BinPacking.Computation.MachineRegularOwnerProgram

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

private theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem oneStep {A : Type} {f : A → Option A} {a b : A}
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
            working (loopData H t v output n) (encodeWord (padding t v - (n + 1))) []⟩ := oneStep guard
      have vertex := vertexTrace H t v ⟨n, h⟩
        (output ++ blocksPrefix (dummyBits H t v) n) (encodeWord (padding t v - (n + 1)))
      have bump := bumpStep H t v n
        ((output ++ blocksPrefix (dummyBits H t v) n) ++ dummyBits H t v ⟨n, h⟩)
        (encodeWord (padding t v - (n + 1)))
      have bumpRun := oneStep bump
      have all := joinTrace (joinTrace (joinTrace first guardRun) vertex) bumpRun
      simpa only [loopSteps, loopFrame, loopData, blocksPrefix_succ _ n h,
        List.append_assoc, Nat.add_assoc] using all

theorem preparationTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[preSteps t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
  joinTrace (joinTrace (metadataTrace H t v output) (copyCountTrace H t v output))
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
      oneStep (loopZeroStep H (loopData H t v output (padding t v)))
  exact joinTrace first last

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
      simpa only [hp] using oneStep (guardZeroStep H (seededData t v output))
    have all := joinTrace (joinTrace prepared gate) (cleanupZeroTrace H t v output hp)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    simp only [ownerTime, cleanupCost, ite_eq_left hp, Nat.add_zero, le_refl]
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.family .start), readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
      oneStep (guardPositiveStep H (seededData t v output) (padding t v) (Nat.pos_of_ne_zero hp))
    have all := joinTrace
      (joinTrace (joinTrace (joinTrace prepared gate) (familyTrace H t v output))
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

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192

noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + regularPolynomial + Polynomial.C q * rowPolynomial q

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)

noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+11)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40986)

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.dummyTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        (((ExpanderFamily.growth+1)*L) + regularPolynomial.eval L)
        ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.dummyTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularDummyRow.timeBound, MachineRegularVertexBlock.rowSizeBound]
  simp only [Nat.add_assoc]

theorem dummyTimeBound_le (q L R x v i k o m O V W R' O' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ O') (hV : V ≤ W) :
    MachineRegularVertexBlock.dummyTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.dummyTimeBound q W R' W W W W W W O' W := by
  unfold MachineRegularVertexBlock.dummyTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularDummyRow.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem ownerPrefix_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) :
    (blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤ regularPolynomial.eval (inputLength t) := by
  have h := PreprocessingRegularBounds.regular_dummyPrefix_le t H v n
  simp only [PreprocessingRegularBounds.dummyPrefix, List.length_append] at h
  omega

theorem growingOutput_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) (output : List Bool) :
    (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤
      (ExpanderFamily.growth+1)*bodySize t output + regularPolynomial.eval (bodySize t output) := by
  have h := (ownerPrefix_length_le H t v n).trans
    (natPolynomial_eval_mono regularPolynomial (Nat.le_add_right (inputLength t) output.length))
  have hO := (wide_le t output).2.2
  rw [List.length_append]
  exact Nat.add_le_add hO h

theorem dummySteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (n : Nat) (output : List Bool) :
    MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let x := paddedNew t (padding t) v j
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hi := (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hk := cloudSize_le_input t v
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have hO := growingOutput_length_le H t v n output
  have raw := MachineRegularVertexBlock.dummySteps_le internalDegree
    MachineRegularOriginalBody.degree_positive t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length
  have bound := dummyTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _ _
    bounds.1 hR (hx.trans bounds.2.1) (hv.trans bounds.1) (hi.trans bounds.2.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) hO
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

noncomputable def prePolynomial : Polynomial Nat :=
  MachineCloudPadding.timePolynomial.comp (2*Polynomial.X+1) + 4*wide + 6

noncomputable def loopPolynomial : Polynomial Nat :=
  wide * (blockPolynomial internalDegree + 2)

noncomputable def cleanupPolynomial : Polynomial Nat :=
  6*wide + rotorPolynomial internalDegree + 13

noncomputable def timePolynomial : Polynomial Nat :=
  prePolynomial + MachineRegularExecutionBounds.familyPolynomial + loopPolynomial +
    cleanupPolynomial + 2

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem loopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    MachineRegularOwnerBody.loopSteps H t v output n hn ≤
      n * ((blockPolynomial internalDegree).eval (bodySize t output) + 2) := by
  induction n with
  | zero => simp only [MachineRegularOwnerBody.loopSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < padding t v := by omega
    have first := ih (by omega)
    have second := dummySteps_le H t v ⟨n, h⟩ n output
    rw [MachineRegularOwnerBody.loopSteps, Nat.succ_mul]
    change MachineRegularOwnerBody.loopSteps H t v output n _ +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v ⟨n, h⟩
        (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
          (familyCloudTable H t) v) n).length + 1) ≤ _
    omega

theorem allLoopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.loopSteps H t v output (padding t v) le_rfl ≤
      loopPolynomial.eval (bodySize t output) := by
  have hd := (cloudTotal_le_input t v).trans (wide_le t output).2.1
  have hp : padding t v ≤ (ExpanderFamily.growth+1)*bodySize t output := by omega
  have h := (loopSteps_le H t v output (padding t v) le_rfl).trans
    (Nat.mul_le_mul_right _ hp)
  simpa only [loopPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

theorem cleanupSteps_working (data : MachineRegularOwnerBody.Data)
    (fuel saved : List Bool) (d : Nat) :
    MachineRegularOwnerCleanup.steps (MachineRegularOwnerBody.working data fuel saved) d =
      2*(d+1) + data.localRank.length + data.count.length + data.rotor.length +
        data.padding.length + data.level.length + fuel.length + 6 := by
  change 2*(d+1) + ((data.localRank.length+1) + ((data.count.length+1) +
    ((data.rotor.length+1) + ((data.padding.length+1) + ((data.level.length+1) +
      ((fuel.length+1)+0)))))) = _
  omega

theorem cleanupCost_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.cleanupCost H t v output ≤
      cleanupPolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := (cloudSize_le_input t v).trans bounds.1
  have htotal := (cloudTotal_le_input t v).trans bounds.2.1
  have hl := (level_le_input t v).trans bounds.1
  have hp : MachineCloudPadding.padding (cloudSize t v) = padding t v := rfl
  by_cases hd : padding t v = 0
  · rw [MachineRegularOwnerBody.cleanupCost, ite_eq_left hd, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, List.length_nil, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · have hpositive : 0 < padding t v := by omega
    have hkpos := PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v ⟨0, hpositive⟩
    have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v hkpos
    change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
    have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
      (natPolynomial_eval_mono (rotorPolynomial internalDegree)
        (Nat.le_add_right (inputLength t) output.length))
    rw [← hrotor] at hR
    change (MachineRegularFamily.rotor H (cloudSize t v)).length ≤
      (rotorPolynomial internalDegree).eval (bodySize t output) at hR
    rw [MachineRegularOwnerBody.cleanupCost, ite_eq_right hd,
      MachineRegularOwnerBody.loopFrame, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.loopData, MachineRegularOwnerBody.vertexData,
      MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, Nat.sub_self, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

theorem ownerTime_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.ownerTime H t v output ≤ timePolynomial.eval (bodySize t output) := by
  have hp := preSteps_le t v output
  have hc := cleanupCost_le H t v output
  have hl := allLoopSteps_le H t v output
  have hf := (MachineRegularExecutionBounds.family_budget_le t v).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial
      (Nat.le_add_right (inputLength t) output.length))
  have hfamily : MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length ≤
      MachineRegularExecutionBounds.familyPolynomial.eval (bodySize t output) := by
    simpa only [bodySize, MachineRegularFamily.timePolynomial, encodeWord_length, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using hf
  simp only [MachineRegularOwnerBody.ownerTime, timePolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat]
  split_ifs <;> omega

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.totalSteps H t v output ≤ timePolynomial.eval (bodySize t output) :=
  (MachineRegularOwnerBody.totalSteps_le H t v output).trans (ownerTime_le H t v output)

noncomputable def ownerInTime (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (MachineRegularOwnerBody.program H))
      (MachineRegularOwnerBody.cfg H (some MachineRegularOwnerBody.entry)
        (MachineRegularOwnerBody.initialData t v output))
      (some (MachineRegularOwnerBody.cfg H none
        (MachineRegularOwnerBody.finalData H t v output)))
      (timePolynomial.eval (bodySize t output)) where
  steps := MachineRegularOwnerBody.totalSteps H t v output
  evals_in_steps := MachineRegularOwnerBody.ownerTrace H t v output
  steps_le_m := totalSteps_le H t v output

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

end OAI

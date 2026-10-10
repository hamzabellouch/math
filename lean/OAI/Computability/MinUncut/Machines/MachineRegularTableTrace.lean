import Mathlib
import OAI.Computability.MinUncut.Estimates.InputData

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open MinUncutGames.Foundations.PCP

private theorem joinCompleteTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

private theorem normalizeEmptyAppend {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinCompleteTrace (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinCompleteTrace (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinCompleteTrace (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i =>
      fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    erw [update_frame_output]; rfl
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

namespace MinUncutGames.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

theorem coreTimeBound_mono (q L R x v i k o m O L' R' x' v' i' k' o' m' O' : Nat)
    (hL : L ≤ L') (hR : R ≤ R') (hx : x ≤ x') (hv : v ≤ v') (hi : i ≤ i')
    (hk : k ≤ k') (ho : o ≤ o') (hm : m ≤ m') (hO : O ≤ O') :
    coreTimeBound q L R x v i k o m O ≤ coreTimeBound q L' R' x' v' i' k' o' m' O' := by
  unfold coreTimeBound
  gcongr

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10 * Polynomial.X +
    2 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) + 13 * Polynomial.X +
    5 * Polynomial.X + Polynomial.C (5*q+10) *
      (Polynomial.X + Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    4 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    2 * regularPolynomial + Polynomial.C (8*q+41066)

theorem corePolynomial_eval (q L : Nat) :
    (corePolynomial q).eval L =
      coreTimeBound q L ((rotorPolynomial q).eval L)
        (ExpanderFamily.growth*L) L (ExpanderFamily.growth*L) L
        (ExpanderFamily.growth*L) L (regularPolynomial.eval L) := by
  simp only [corePolynomial, coreTimeBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

theorem internal_steps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v) (p : Fin q)
    (outputLength : Nat) (houtput : outputLength ≤ regularPolynomial.eval (inputLength t)) :
    coreSteps t (padding t) tables v x p outputLength ≤
      (corePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  rw [corePolynomial_eval]
  exact (coreSteps_le q positive t (padding t) tables v x p outputLength).trans
    (coreTimeBound_mono q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le_rfl
      (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
      (prefix_le_input t v.val) hm houtput)

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

theorem family_budget_le (t : GraphTables.Table) (v : Fin t.vertices) :
    MachinePaddedExpanderFamilyBounds.timePolynomial.eval (cloudSize t v + 1) +
      2 * ExpanderFamily.growth * (cloudSize t v + 1) + 7 ≤
        familyPolynomial.eval (inputLength t) := by
  have h := Nat.add_le_add_right (cloudSize_le_input t v) 1
  have hp := natPolynomial_eval_mono MachinePaddedExpanderFamilyBounds.timePolynomial h
  have hm := Nat.mul_le_mul_left (2 * ExpanderFamily.growth) h
  simp only [familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  omega

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * Polynomial.X +
    (Polynomial.C ExpanderFamily.growth * Polynomial.X) * Polynomial.C (q + 1) + 8192

theorem rowPolynomial_eval (q L : Nat) :
    (rowPolynomial q).eval L =
      ExpanderFamily.growth * L + (ExpanderFamily.growth * L) * (q + 1) + 8192 := by
  simp only [rowPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem actual_row_bound_le (q : Nat) (t : GraphTables.Table) :
    vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192 ≤
      (rowPolynomial q).eval (inputLength t) := by
  rw [rowPolynomial_eval]
  have h := regularVertices_le_input t
  exact Nat.add_le_add_right (Nat.add_le_add h (Nat.mul_le_mul_right _ h)) _

noncomputable def blockCorePolynomial (q : Nat) : Polynomial Nat :=
  corePolynomial q + Polynomial.C (2*q) * rowPolynomial q

theorem coreTimeBound_add_output (q L R x v i k o m O A : Nat) :
    coreTimeBound q L R x v i k o m (O + A) =
      coreTimeBound q L R x v i k o m O + 2*A := by
  unfold coreTimeBound
  omega

theorem block_core_bound_le (q : Nat) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v)
    (initialOutput : Nat) (houtput : initialOutput ≤ regularPolynomial.eval (inputLength t)) :
    coreTimeBound q (GraphTables.tableBits t).length
      (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
      (vertexOrder t (padding t) x.val).val v.val (paddedCloudRank t (padding t) v x).val
      (cloudSize t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) t.darts
      (initialOutput + q *
        (vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192)) ≤
      (blockCorePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hr := Nat.mul_le_mul_left q (actual_row_bound_le q t)
  have hO := Nat.add_le_add houtput hr
  have h := coreTimeBound_mono q (inputLength t) _ _ _ _ _ _ _ _
    (inputLength t) _ _ _ _ _ _ _ _ le_rfl
    (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
    (prefix_le_input t v.val) hm hO
  simp only [coreTimeBound_add_output] at h ⊢
  rw [← corePolynomial_eval] at h
  simpa only [inputLength, blockCorePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Nat.mul_assoc] using h

end MinUncutGames.Foundations.Complexity.MachineRegularExecutionBounds

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192
noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + Polynomial.C q * rowPolynomial q
noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)
noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+20)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40995)
noncomputable def cleanupPolynomial (q : Nat) : Polynomial Nat := 6*wide + rotorPolynomial q + 13
noncomputable def timePolynomial : Polynomial Nat :=
  MachineRegularMetadata.timePolynomial + MachineRegularExecutionBounds.familyPolynomial +
    blockPolynomial internalDegree + cleanupPolynomial internalDegree

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.originalTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.originalTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularOriginalClean.timeBound, MachineRegularVertexBlock.rowSizeBound]
  ring

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
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

theorem vertexSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalBody.vertexSteps H t e output ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := e.isLt.le.trans (GraphTables.darts_le_tableBits_length t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have raw := MachineRegularVertexBlock.originalSteps_le internalDegree degree_positive
    t (padding t) (familyCloudTable H t) e output.length
  have bound := originalTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _
    bounds.1 hR (hx.trans bounds.1) (hv.trans bounds.1) (hi.trans bounds.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) bounds.2.2
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem clearSteps_frame (data : Data) :
    clearSteps (frame data) 7 = data.owner.length + data.localRank.length +
      data.count.length + data.offset.length + data.rotor.length + data.padding.length +
      data.level.length + 7 := by
  simp [clearSteps, clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  omega

theorem cleanupSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    clearSteps (frame (emittedData H t e output)) 7 ≤
      (cleanupPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  have bounds := wide_le t output
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have ho := prefix_le_input t v.val
  have hp := cloudTotal_le_input t v
  have hl := level_le_input t v
  have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
    (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  rw [← hrotor] at hR
  rw [clearSteps_frame]
  simp only [emittedData, familyData, metadataData, MachineRegularMetadata.originalData,
    MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
    MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData, initialData,
    encodeWord_length, cleanupPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  change _ ≤ 6*((ExpanderFamily.growth+1)*bodySize t output) +
    (rotorPolynomial internalDegree).eval (bodySize t output)+13
  change cloudSize t v + MachineCloudPadding.padding (cloudSize t v) ≤ _ at hp
  dsimp only [v, bodySize, inputLength] at *
  omega

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

noncomputable def originalInTime (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t e output))
      (some (cfg H none (initialData t e (output ++ emittedBits H t e))))
      (timePolynomial.eval (bodySize t output)) where
  steps := totalSteps H t e output
  evals_in_steps := originalTrace H t e output
  steps_le_m := totalSteps_le H t e output

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

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

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

namespace MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds

noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end MinUncutGames.Foundations.Complexity.MachineRegularTable.Top

end OAI

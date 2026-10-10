import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularOriginalBody
import OAI.Combinatorics.IndependentSets.Machines.Machine2

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularExecutionBounds

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

end IndependentSetsGames.Foundations.Complexity.MachineRegularExecutionBounds
namespace IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

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

end IndependentSetsGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

end OAI

import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachinePaddedOverlayRuntimeLemmas
import OAI.Computability.UniqueGames.Machines.MachineRegularOriginalBody

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

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

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI

import Mathlib
import OAI.MathematicalPhysics.BFSS.OscillatorLimits
import OAI.MathematicalPhysics.BFSS.NormalFields

namespace OAI

/-! Normal core energy identities, positivity and compact multipliers. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Finset
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2
local instance oscillatorFormsOperatorNormedAddCommGroup : NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance oscillatorFormsOperatorNormedSpace : NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

def normalChargeField (q : Boson N) (α : SpinIndex) :
    M.NormalCoordinates q →L[ℝ] (Fermion N →L[ℝ] Fermion N) :=
  (M.normalLinearField q α).comp ((M.normalSlice q).subtypeL.comp
    (M.normalCoordinateIsometry q).toContinuousLinearEquiv.toContinuousLinearMap)

lemma normalChargeField_apply (q : Boson N) (α : SpinIndex) (x : M.NormalCoordinates q) :
    M.normalChargeField q α x = M.normalLinearField q α (M.normalCoordinateIsometry q x) := rfl

lemma normalChargeField_basis (q : Boson N) (α : SpinIndex) (i : M.NormalIndex q) :
    M.normalChargeField q α (EuclideanSpace.single i 1) =
      M.normalLinearField q α (M.normalBasisVector q i) := by
  simp only [M.normalChargeField_apply,normalCoordinateIsometry,
    OrthonormalBasis.repr_symm_single,normalBasisVector]

abbrev NormalCore (q : Boson N) := BFSSSliceSobolev.Core (E := M.NormalCoordinates q) (F := Fermion N)

def normalCoreCharge (q : Boson N) (α : SpinIndex) (f : M.NormalCore q) : M.NormalCore q :=
  MixedEnergy.firstOrder (M.normalKineticSkewSymbol q α) f +
    MixedEnergy.field (M.normalChargeField q α) (M.normalChargeField q α).contDiff f

lemma normalSkewCore_apply (q : Boson N) (α : SpinIndex) (f : M.NormalCore q)
    (x : M.NormalCoordinates q) :
    MixedEnergy.firstOrder (M.normalKineticSkewSymbol q α) f x =
      (-Complex.I) • BFSSKinetic.kineticDerivative (M.normalKineticSymbol q α) f x := by
  rw [MixedEnergy.firstOrder_apply,BFSSKinetic.kineticDerivative_apply]
  simp only [normalKineticSkewSymbol,kineticSkewLinear,normalKineticSymbol,
    ContinuousLinearMap.coe_restrictScalars',
    Finset.smul_sum,_root_.sum_apply,BFSSKinetic.post_apply]
  rfl

lemma normalSkewCore_norm (q : Boson N) (α : SpinIndex) (f : M.NormalCore q) :
    ‖MixedEnergy.toL2 (MixedEnergy.firstOrder (M.normalKineticSkewSymbol q α) f)‖^2 =
      (1/2 : ℝ)*‖BFSSSliceSobolev.gradient volume
        (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f‖^2 := by
  have he : ‖MixedEnergy.toL2 (MixedEnergy.firstOrder (M.normalKineticSkewSymbol q α) f)‖^2 =
      ‖BFSSKinetic.toL2 (BFSSKinetic.kineticDerivative (M.normalKineticSymbol q α) f)‖^2 := by
    change ‖BFSSSliceSobolev.toL2 volume _‖^2 = ‖BFSSSliceSobolev.toL2 volume _‖^2
    rw [BFSSSliceSobolev.toL2_norm_sq,BFSSSliceSobolev.toL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [M.normalSkewCore_apply,norm_smul]
    norm_num only [norm_neg,Complex.norm_I,one_mul]
  rw [he,BFSSKinetic.kinetic_norm_sq _ (M.normalKineticSymbol_selfAdjoint q α)
    (M.normalKineticSymbol_CAR q α),PiLp.norm_sq_eq_of_L2]
  apply congrArg (fun t : ℝ => (1/2 : ℝ)*t)
  apply Finset.sum_congr rfl
  intro i _
  simp only [BFSSSliceSobolev.gradient_apply,EuclideanSpace.basisFun_apply]
  rfl

lemma normalRemainderField_apply (q : Boson N) (hq : q ∈ M.massiveZeros)
    (x : M.NormalCoordinates q) (u : Fermion N) :
    (1/16 : ℝ) • MixedEnergy.remainderField (M.normalKineticSkewSymbol q)
      (fun α => M.normalChargeField q α) x u = M.deformedFermionField 1 1 q u := by
  simp only [MixedEnergy.remainderField,ContinuousLinearMap.fderiv,
    _root_.sum_apply,mul_apply_eq_comp,M.normalChargeField_basis]
  exact M.normalFermion_contraction q hq u

theorem normalCore_energy_identity (q : Boson N) (hq : q ∈ M.massiveZeros) (f : M.NormalCore q) :
    (1/16 : ℝ)*∑ α : SpinIndex, ‖MixedEnergy.toL2 (M.normalCoreCharge q α f)‖^2 =
      (1/2 : ℝ)*‖BFSSSliceSobolev.gradient volume
        (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f‖^2 +
      (∫ x : M.NormalCoordinates q,
        M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)*‖f x‖^2) +
      (∫ x : M.NormalCoordinates q, inner ℝ (f x) (M.deformedFermionField 1 1 q (f x))) := by
  have hid := MixedEnergy.averaged_energy_identity (M.normalKineticSkewSymbol q)
    (fun α i u v => M.kineticSkewLinear_skew α (M.normalBasisVector q i) u v)
    (fun α => M.normalChargeField q α) (fun α => (M.normalChargeField q α).contDiff)
    (fun α x => M.normalLinearField_selfAdjoint q (M.normalCoordinateIsometry q x) α) f
  have hk : (∑ α : SpinIndex, ‖MixedEnergy.toL2
      (MixedEnergy.firstOrder (M.normalKineticSkewSymbol q α) f)‖^2) =
      8*‖BFSSSliceSobolev.gradient volume
        (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f‖^2 := by
    simp only [M.normalSkewCore_norm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      SpinIndex,nsmul_eq_mul]
    ring
  have hp : (1/16 : ℝ)*(∑ α : SpinIndex, ‖MixedEnergy.toL2
      (MixedEnergy.field (M.normalChargeField q α) (M.normalChargeField q α).contDiff f)‖^2) =
      ∫ x : M.NormalCoordinates q,
        M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)*‖f x‖^2 := by
    change (1/16 : ℝ)*(∑ α : SpinIndex, ‖BFSSSliceSobolev.toL2 volume
      (MixedEnergy.field (M.normalChargeField q α) (M.normalChargeField q α).contDiff f)‖^2) = _
    simp_rw [BFSSSliceSobolev.toL2_norm_sq]
    rw [←integral_finsetSum _ (fun α _ => (MixedEnergy.inner_integrable
      (MixedEnergy.field (M.normalChargeField q α) (M.normalChargeField q α).contDiff f)
      (MixedEnergy.field (M.normalChargeField q α) (M.normalChargeField q α).contDiff f)).congr
      (Filter.Eventually.of_forall (fun x => real_inner_self_eq_norm_sq _))),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    exact M.normalLinearField_potential_average q (M.normalCoordinateIsometry q x) hq (f x)
  have hanti (x : M.NormalCoordinates q) (i : M.NormalIndex q) :
      (∑ α : SpinIndex, (M.normalKineticSkewSymbol q α i * M.normalChargeField q α x +
        M.normalChargeField q α x * M.normalKineticSkewSymbol q α i)) = 0 :=
    M.normalLinearField_anticommutator_linear q (M.normalCoordinateIsometry q x) (M.normalBasisVector q i)
  have hf : (1/16 : ℝ)*inner ℝ (MixedEnergy.toL2 f)
      (MixedEnergy.toL2 (MixedEnergy.remainderCore (M.normalKineticSkewSymbol q)
        (fun α => M.normalChargeField q α) (fun α => (M.normalChargeField q α).contDiff) f)) =
      ∫ x : M.NormalCoordinates q, inner ℝ (f x) (M.deformedFermionField 1 1 q (f x)) := by
    rw [MixedEnergy.toL2_inner,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [MixedEnergy.remainderCore_apply _ _ _ hanti,←real_inner_smul_right,
      M.normalRemainderField_apply q hq]
  change (1/16 : ℝ)*_ = _
  rw [show (∑ α : SpinIndex, ‖MixedEnergy.toL2 (M.normalCoreCharge q α f)‖^2) = _ from hid]
  rw [mul_add,mul_add,hk,hp,hf]
  ring

theorem normalOscillator_core_nonneg (q : Boson N) (hq : q ∈ M.massiveZeros) (f : M.NormalCore q) :
    0 ≤ M.normalOscillatorForm q (BFSSSliceSobolev.toL2 volume f)
      (BFSSSliceSobolev.gradient volume (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f) := by
  have h := M.normalCore_energy_identity q hq f
  have hp : (∫ x : M.NormalCoordinates q, M.normalQuadratic q
      (M.normalCoordinateIsometry q x : Boson N)*‖(BFSSSliceSobolev.toL2 volume f) x‖^2) =
      ∫ x : M.NormalCoordinates q, M.normalQuadratic q
      (M.normalCoordinateIsometry q x : Boson N)*‖f x‖^2 := by
    apply integral_congr_ae
    filter_upwards [BFSSSliceSobolev.toL2_ae volume f] with x hx
    rw [hx]
  have hf : (∫ x : M.NormalCoordinates q, inner ℝ ((BFSSSliceSobolev.toL2 volume f) x)
      (M.deformedFermionField 1 1 q ((BFSSSliceSobolev.toL2 volume f) x))) =
      ∫ x : M.NormalCoordinates q, inner ℝ (f x) (M.deformedFermionField 1 1 q (f x)) := by
    apply integral_congr_ae
    filter_upwards [BFSSSliceSobolev.toL2_ae volume f] with x hx
    rw [hx]
  rw [normalOscillatorForm,hp,hf,←h]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun α _ => sq_nonneg _))
end
end BFSSQuantum.AlgebraData

namespace BFSSLocalL2
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure E}

def compactBound (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) : ℝ :=
  max 0 (hc.exists_bound_of_continuous hw).choose

omit [MeasurableSpace E] [BorelSpace E] in
lemma compactBound_nonneg (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) :
    0 ≤ compactBound w hw hc := le_max_left _ _

omit [MeasurableSpace E] [BorelSpace E] in
lemma compactBound_bound (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) (x : E) :
    |w x| ≤ compactBound w hw hc :=
  (hc.exists_bound_of_continuous hw).choose_spec x |>.trans (le_max_right _ _)

def compactMul (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (u : Lp F 2 μ) : Lp F 2 μ :=
  boundedMul w hw.aestronglyMeasurable (compactBound w hw hc)
    (ae_of_all μ (compactBound_bound w hw hc)) u

lemma compactMul_ae (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (u : Lp F 2 μ) : (compactMul w hw hc u : E → F) =ᵐ[μ] fun x => w x • u x :=
  boundedMul_ae _ _ _ _ _

lemma compactMul_continuous (w : E → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) :
    Continuous (compactMul (F := F) (μ := μ) w hw hc) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨compactBound w hw hc,compactBound_nonneg w hw hc⟩) ?_).continuous
  intro u v
  exact boundedMul_dist_le w hw.aestronglyMeasurable _ (compactBound_nonneg w hw hc) _ u v
end
end BFSSLocalL2

end OAI

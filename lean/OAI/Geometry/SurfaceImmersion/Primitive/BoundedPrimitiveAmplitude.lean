import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeParameterBounds

namespace OAI

/-! Uniform inverse and amplitude bounds from the fixed reference size and
positive coefficient margin. Inactive chart coefficients need not vary continuously. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance boundedAmplitudeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance boundedAmplitudeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance boundedAmplitudeDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedAmplitudeDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedAmplitudeGroup : AddCommGroup TensorFiber := boundedAmplitudeFiberNormed.toAddCommGroup
local instance boundedAmplitudeComplete : CompleteSpace TensorFiber := inferInstance
local instance boundedFiberFinite : FiniteDimensional ℝ TensorFiber := inferInstance
local instance boundedDualFinite : FiniteDimensional ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFinite : FiniteDimensional ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance boundedDualFamilyFinite : FiniteDimensional ℝ (ι → TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFamilyFinite : FiniteDimensional ℝ (ι → Plane →L[ℝ] ℝ) := inferInstance
local instance boundedOperatorDataFinite : FiniteDimensional ℝ (PrimitiveOperatorData ι) := inferInstance
local instance boundedDataFinite : FiniteDimensional ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataProper : ProperSpace (PrimitiveAmplitudeData ι) :=
  FiniteDimensional.proper ℝ (PrimitiveAmplitudeData ι)
local instance boundedDataNormed : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance

def boundedPrimitiveReference (i : ι) (D k : ℝ) : Set (PrimitiveAmplitudeData ι) :=
  {z | ‖z‖ ≤ D ∧ primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber ∧
      k ≤ z.1.1.1 i z.2}

lemma boundedPrimitiveReference_compact (i : ι) (D k : ℝ) :
    IsCompact (boundedPrimitiveReference i D k) := by
  have hq : Continuous (fun z : PrimitiveAmplitudeData ι => z.1.1.1 i z.2) := by
    have h : Continuous (fun z : PrimitiveAmplitudeData ι => z.1.1.1 i) := by fun_prop
    exact h.clm_apply continuous_snd
  have hclosed : IsClosed (boundedPrimitiveReference i D k) :=
    (isClosed_le continuous_norm continuous_const).inter
      ((isClosed_eq (primitiveDataOperator_smooth.continuous.comp continuous_fst) continuous_const).inter
        (isClosed_le continuous_const hq))
  exact (isCompact_closedBall (0 : PrimitiveAmplitudeData ι) D).of_isClosed_subset
    hclosed (fun z hz => by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1)

lemma boundedPrimitiveReference_good (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k)
    {z : PrimitiveAmplitudeData ι} (hz : z ∈ boundedPrimitiveReference i D k) :
    (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient i z := by
  change (primitiveDataOperator z.1).IsInvertible ∧
    0 < z.1.1.1 i ((primitiveDataOperator z.1).inverse z.2)
  rw [hz.2.1,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_apply]
  exact ⟨⟨ContinuousLinearEquiv.refl ℝ TensorFiber,rfl⟩,hk.trans_le hz.2.2⟩

theorem bounded_primitive_amplitude_C1 (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
      ∀ z : PrimitiveAmplitudeData ι, ‖z‖ ≤ D →
      primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber →
      k ≤ z.1.1.1 i z.2 → ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
        (primitiveDataOperator z'.1).IsInvertible ∧
        0 < primitiveParameterCoefficient i z' ∧
        ‖primitiveParameterInverse z'‖ ≤ C ∧
        ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
        |primitiveParameterAmplitude i z'| ≤ C ∧
        ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C := by
  obtain ⟨eps,C,heps,hC,hbound⟩ := compact_primitive_amplitude_C1 i
    (boundedPrimitiveReference_compact i D k)
    (fun _ hz => boundedPrimitiveReference_good i D hk hz)
  exact ⟨eps,C,heps,hC,fun z hn hi hp z' hd => hbound z ⟨hn,hi,hp⟩ z' hd⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFiberInverse
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance dataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance dataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance dataFiberComplete : CompleteSpace TensorFiber := inferInstance
local instance dataDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance dataDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance dataFiberGroup : AddCommGroup TensorFiber := dataFiberNormed.toAddCommGroup
variable {ι : Type*} [Fintype ι]

abbrev PrimitiveOperatorData (ι : Type*) :=
  ((ι → TensorFiber →L[ℝ] ℝ) × (ι → ℝ)) × (ι → Plane →L[ℝ] ℝ)

def primitiveDataOperator (z : PrimitiveOperatorData ι) : TensorFiber →L[ℝ] TensorFiber :=
  completedPrimitiveOperator z.1.1 z.1.2 z.2

lemma primitiveDataOperator_smooth :
    ContDiff ℝ ∞ (primitiveDataOperator (ι := ι)) := by
  have hs : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
      finitePrimitiveOperator z.1.1 z.1.2 z.2) := by
    apply ContDiff.sum
    intro i _
    have hp : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.1.2 i) :=
      (contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_fst)
    have hv : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.2 i) :=
      (contDiff_apply ℝ (Plane →L[ℝ] ℝ) i).comp contDiff_snd
    have hq : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
        (z.1.1 i).comp tensorSymmetrizer) :=
      ((contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
        (contDiff_fst.comp contDiff_fst)).clm_comp contDiff_const
    exact (hp.pow 2).smul (hq.smulRight (hv.smulRight hv))
  exact (hs.add contDiff_const).sub contDiff_const

lemma primitiveDataInverse_smoothAt {z : PrimitiveOperatorData ι}
    (hz : (primitiveDataOperator z).IsInvertible) (H : TensorFiber) :
    ContDiffAt ℝ ∞ (fun w : PrimitiveOperatorData ι × TensorFiber =>
      (primitiveDataOperator w.1).inverse w.2) (z, H) := by
  exact (hz.contDiffAt_map_inverse.comp (z,H)
    (primitiveDataOperator_smooth.contDiffAt.comp (z,H) contDiffAt_fst)).clm_apply contDiffAt_snd

lemma isOpen_primitiveDataPositive (i : ι) :
    IsOpen {w : PrimitiveOperatorData ι × TensorFiber |
      (primitiveDataOperator w.1).IsInvertible ∧
      0 < w.1.1.1 i ((primitiveDataOperator w.1).inverse w.2)} := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hop : ContinuousAt (fun z : PrimitiveOperatorData ι × TensorFiber =>
      primitiveDataOperator z.1) w :=
    (primitiveDataOperator_smooth.continuous.comp continuous_fst).continuousAt
  have hi := hop.eventually hw.1.eventually_nhds
  have hinv := (hw.1.contDiffAt_map_inverse (n := ∞)).continuousAt.comp (x := w) hop
  have hval := hinv.clm_apply continuous_snd.continuousAt
  have hcoeff : Continuous (fun z : PrimitiveOperatorData ι × TensorFiber => z.1.1.1 i) := by
    fun_prop
  exact hi.and ((hcoeff.continuousAt.clm_apply hval).eventually (lt_mem_nhds hw.2))

/-- On a compact family of exact reference decompositions, independent
perturbations of every entry preserve invertibility and the selected positive
amplitude coefficient. In particular the coefficient functionals may vary. -/
theorem compact_primitiveData_stability (i : ι)
    {K : Set (PrimitiveOperatorData ι × TensorFiber)} (hK : IsCompact K)
    (hid : ∀ w ∈ K, primitiveDataOperator w.1 = ContinuousLinearMap.id ℝ TensorFiber)
    (hpos : ∀ w ∈ K, 0 < w.1.1.1 i w.2) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ w ∈ K, ∀ w' : PrimitiveOperatorData ι × TensorFiber,
      ‖w'-w‖ < eps → (primitiveDataOperator w'.1).IsInvertible ∧
        0 < w'.1.1.1 i ((primitiveDataOperator w'.1).inverse w'.2) := by
  have hsub : K ⊆ {w : PrimitiveOperatorData ι × TensorFiber |
      (primitiveDataOperator w.1).IsInvertible ∧
      0 < w.1.1.1 i ((primitiveDataOperator w.1).inverse w.2)} := by
    intro w hw
    change (primitiveDataOperator w.1).IsInvertible ∧
      0 < w.1.1.1 i ((primitiveDataOperator w.1).inverse w.2)
    rw [hid w hw,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_apply]
    exact ⟨⟨ContinuousLinearEquiv.refl ℝ TensorFiber,rfl⟩,hpos w hw⟩
  obtain ⟨eps,heps,hnear⟩ := hK.exists_thickening_subset_open
    (isOpen_primitiveDataPositive i) hsub
  refine ⟨eps,heps,fun w hw w' hdist => hnear ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hdist⟩


/-- A local matrix and the one active coefficient are enough for compact
stability. No continuity of inactive chart functionals is required. -/
theorem compact_inverse_coefficient_stability
    {K : Set (((TensorFiber →L[ℝ] TensorFiber) × (TensorFiber →L[ℝ] ℝ)) × TensorFiber)}
    (hK : IsCompact K)
    (hid : ∀ w ∈ K, w.1.1 = ContinuousLinearMap.id ℝ TensorFiber)
    (hpos : ∀ w ∈ K, 0 < w.1.2 w.2) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ w ∈ K,
      ∀ w' : ((TensorFiber →L[ℝ] TensorFiber) × (TensorFiber →L[ℝ] ℝ)) × TensorFiber,
      ‖w'-w‖ < eps → w'.1.1.IsInvertible ∧ 0 < w'.1.2 (w'.1.1.inverse w'.2) := by
  let O : Set (((TensorFiber →L[ℝ] TensorFiber) × (TensorFiber →L[ℝ] ℝ)) × TensorFiber) :=
    {w | w.1.1.IsInvertible ∧ 0 < w.1.2 (w.1.1.inverse w.2)}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hop : ContinuousAt (fun z : ((TensorFiber →L[ℝ] TensorFiber) ×
        (TensorFiber →L[ℝ] ℝ)) × TensorFiber => z.1.1) w :=
      continuous_fst.fst.continuousAt
    have hi := hop.eventually hw.1.eventually_nhds
    have hinv := (hw.1.contDiffAt_map_inverse (n := ∞)).continuousAt.comp (x := w) hop
    have hval := hinv.clm_apply continuous_snd.continuousAt
    have hcoeff : Continuous (fun z : ((TensorFiber →L[ℝ] TensorFiber) ×
        (TensorFiber →L[ℝ] ℝ)) × TensorFiber => z.1.2) := continuous_fst.snd
    exact hi.and ((hcoeff.continuousAt.clm_apply hval).eventually (lt_mem_nhds hw.2))
  have hKO : K ⊆ O := by
    intro w hw
    change w.1.1.IsInvertible ∧ 0 < w.1.2 (w.1.1.inverse w.2)
    rw [hid w hw,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_apply]
    exact ⟨⟨ContinuousLinearEquiv.refl ℝ TensorFiber,rfl⟩,hpos w hw⟩
  obtain ⟨eps,heps,hnear⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨eps,heps,fun w hw w' hdist => hnear ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hdist⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

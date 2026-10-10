import OAI.Geometry.SurfaceImmersion.Atlas.TensorRootPhases
import OAI.Geometry.Immersion.ClosedSurface.MetricCoordinates

namespace OAI

/-! Restored rank-one tensor coordinates are the actual differentials of
atlas phases. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry

local instance phaseDifferentialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseDifferentialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance phaseDifferentialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDifferentialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseDifferentialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseDifferentialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorComponent_apply (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : Plane) :
    A.bundleComponent A.tensorTriv i u p v w =
      u p ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symm p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symm p w) := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ ht ht (mem_univ p)]
  simp

lemma tensorComponent_tangentCoordinates (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : TangentSpace planeModel p) :
    A.bundleComponent A.tensorTriv i u p
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
      u p v w := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  rw [A.tensorComponent_apply i u hp]
  rw [← Trivialization.symmL_apply (R := ℝ) _ ht, ← Trivialization.symmL_apply (R := ℝ) _ ht,
    Trivialization.symmL_continuousLinearMapAt _ ht, Trivialization.symmL_continuousLinearMapAt _ ht]

lemma tensorRestore_apply (i : A.centers) (f : JetPolynomial.Base → TensorFiber)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : TangentSpace planeModel p) :
    A.bundleRestore A.tensorTriv i f p v w = A.outer i p *
      f (chart (i : M) p)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) := by
  rw [← A.tensorComponent_tangentCoordinates i (A.bundleRestore A.tensorTriv i f) hp]
  have hc : A.bundleComponent A.tensorTriv i (A.bundleRestore A.tensorTriv i f) p =
      A.outer i p • f (chart (i : M) p) := by
    change (A.tensorTriv i).continuousLinearMapAt ℝ p
      (A.outer i p • (A.tensorTriv i).symmL ℝ p (f (chart (i : M) p))) = _
    rw [map_smul, (A.tensorTriv i).continuousLinearMapAt_symmL (A.tensorTriv_domain i hp)]
  rw [hc]
  rfl

lemma coordinateChart_tangentCoordinates (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ, SmallModes.Base) (coordinateChart (i : M)) p =
      planeCoordinates.toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hp' : p ∈ (chartAt Plane (i : M)).source := by simpa only [chart_source] using hp
  have hcs : ContMDiffOn planeModel planeModel ∞ (chartAt Plane (i : M))
      (chartAt Plane (i : M)).source := contMDiffOn_chart
  have hc := (hcs p hp').contMDiffAt ((chartAt Plane (i : M)).open_source.mem_nhds hp')
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp']
  change mfderiv planeModel 𝓘(ℝ, SmallModes.Base) (planeCoordinates ∘ chartAt Plane (i : M)) p =
    planeCoordinates.toContinuousLinearMap.comp (mfderiv planeModel planeModel (chartAt Plane (i : M)) p)
  rw [mfderiv_comp p
    (((planeCoordinates.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)).mdifferentiableAt)
    (hc.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, planeCoordinates.fderiv]
  rfl

lemma tensorRestore_covectorSquare (i : A.centers) (ξ : SmallModes.Base)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : TangentSpace planeModel p) :
    A.bundleRestore A.tensorTriv i (fun _ => fiberFromThree (covectorSquare ξ)) p v w =
      A.outer i p * (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (i : M) ξ) p v) *
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (i : M) ξ) p w) := by
  have hp' : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source, chart_source] using hp
  rw [A.tensorRestore_apply i _ hp, fiberFromThree_apply, covectorSquare_evaluate,
    mfderiv_atlasPhase _ _ hp', A.coordinateChart_tangentCoordinates i hp]
  exact (mul_assoc _ _ _).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

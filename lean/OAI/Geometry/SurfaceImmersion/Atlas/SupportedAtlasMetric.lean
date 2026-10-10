import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasDifferential
import OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDifferential

namespace OAI

/-! Actual metric and linearized metric of supported restored displacements
in the original atlas coordinates. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4
open FiniteOrderSmoothing JetPolynomial

lemma surfaceDifferential_zero_off_support
    {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M → V) {p : M}
    (hp : p ∉ tsupport F) : surfaceDifferential F p = 0 := by
  have he : F =ᶠ[𝓝 p] (fun _ => (0 : V)) := notMem_tsupport_iff_eventuallyEq.mp hp
  unfold surfaceDifferential
  rw [he.mfderiv_eq, mfderiv_const]
  exact ContinuousLinearMap.comp_zero _

lemma euclidean_metric_coordinate_value (f : SmallModes.Base → Space)
    {y : SmallModes.Base} (hf : DifferentiableAt ℝ f y) (v w : SmallModes.Base) :
    PhaseMean.evaluate (RealModes.realMetricTensor (spaceCoordinates ∘ f) y) v w =
      inner ℝ (fderiv ℝ f y v) (fderiv ℝ f y w) := by
  rw [RealModes.evaluate_realMetricTensor]
  simp only [RealModes.realMetric, SmallModes.coordDeriv]
  rw [(spaceCoordinates.hasFDerivAt.comp y hf.hasFDerivAt).fderiv]
  exact spaceCoordinates_dot _ _

namespace FiniteOrderSmoothing.SmoothingAtlas
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable (A : SmoothingAtlas M)

lemma restore_plane_metric_on_source (i : A.centers) (f : SmallModes.Base → Space)
    (hf : tsupport f ⊆ (Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (hd : DifferentiableAt ℝ f (planeCoordinateIsometry (chart (i : M) p)))
    (v w : TangentSpace planeModel p) :
    inducedForm (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p v w =
      PhaseMean.evaluate
        (RealModes.realMetricTensor (spaceCoordinates ∘ f)
          (planeCoordinateIsometry (chart (i : M) p)))
        (planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v))
        (planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w)) := by
  rw [euclidean_metric_coordinate_value f hd]
  unfold inducedForm
  have he := A.restore_plane_mfderiv i f hf hp hd
  change surfaceDifferential (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p = _ at he
  rw [he]
  rfl

lemma restore_plane_metric_off_support (i : A.centers) (f : SmallModes.Base → Space)
    (hf : tsupport f ⊆ (Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∉ tsupport (A.weight i)) (v w : TangentSpace planeModel p) :
    inducedForm (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p v w = 0 := by
  have hzero := surfaceDifferential_zero_off_support
    (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))
    (fun h => hp (A.restore_plane_tsupport i f hf h))
  simp only [inducedForm,hzero,zero_apply,inner_zero_right]

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorPullback
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

namespace OAI

/-! Positivity of the prescribed metric survives the actual inverse phase
chart. In particular its curvature denominator is nonzero on the active
chart locus. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_positive (i : A.centers) (g : SmoothMetric M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) (hactive : A.chartWeight i (e.symm p) ≠ 0) :
    0 < A.phaseMetricRead i e.symm g (baseEquiv p) 0 ∧
      0 < A.phaseMetricRead i e.symm g (baseEquiv p) 0 *
        A.phaseMetricRead i e.symm g (baseEquiv p) 2 -
          (A.phaseMetricRead i e.symm g (baseEquiv p) 1)^2 := by
  have hpt : e.symm p ∈ (A.chartWeightCompact i : Set JetPolynomial.Base) := by
    rw [← A.chartWeight_tsupport i]
    exact subset_tsupport (A.chartWeight i) hactive
  have hmode : planeCoordinateIsometry (e.symm p) ∈
      (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    ⟨e.symm p,hpt,rfl⟩
  have hm := A.tensorPlaneRead_metric g i hmode
  have hpositive := coordinateMetric_positive g (i : M) (A.modeSupport_subset_coordinateDomain i hmode)
  have hold : 0 < A.tensorChartRead i g.inner (e.symm p) 0 ∧
      0 < A.tensorChartRead i g.inner (e.symm p) 0 * A.tensorChartRead i g.inner (e.symm p) 2 -
        (A.tensorChartRead i g.inner (e.symm p) 1)^2 := by
    rw [← hm] at hpositive
    simpa only [tensorPlaneRead,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hpositive
  have hinv : e ∘ e.symm =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_target.mem_nhds hp] with q hq
    exact e.right_inv hq
  have hcomp : (fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p) =
      ContinuousLinearMap.id ℝ JetPolynomial.Base := by
    rw [← fderiv_comp p (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
      hinv.fderiv_eq,fderiv_id]
  have hdi : Function.Injective (fderiv ℝ e.symm p) := by
    intro u v huv
    have hh := congrArg (fderiv ℝ e (e.symm p)) huv
    change ((fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p)) u =
      ((fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p)) v at hh
    simpa only [hcomp,ContinuousLinearMap.id_apply] using hh
  have hL : Function.Injective (tensorCoordinateDerivative e.symm p) :=
    planeCoordinateIsometry.injective.comp (hdi.comp planeCoordinateIsometry.symm.injective)
  have hh := PhaseMean.positive_pullback (tensorCoordinateDerivative e.symm p) hL hold
  simpa only [phaseMetricRead,baseEquiv.symm_apply_apply,tensorCoordinatePullbackValue] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.PureRadialGauss

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_isometry_det (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    gramDet (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i T F) p)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i T F) p) =
    A.phaseMetricRead i T g p 0 * A.phaseMetricRead i T g p 2 -
      (A.phaseMetricRead i T g p 1)^2 := by
  have hm := A.phaseMetricRead_isometry i hT hF (p := baseEquiv.symm p) hp
  rw [baseEquiv.apply_symm_apply] at hm
  have hh := congrArg (fun H : PhaseMean.Tensor => H 0*H 2-(H 1)^2) hm
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame
lemma coordinateGauss_eq_curvature_mul (F : RField 4) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p *
        gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  change _ = (_ / gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * _
  exact (div_mul_cancel₀ _ hD).symm
end ClosedSurfaceR4.RealModes

end

end OAI

import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricRead
import OAI.Geometry.SurfaceImmersion.Atlas.JetMetricCoordinatePullback
import OAI.Geometry.SurfaceImmersion.Atlas.TensorCoordinatePullbackBounds
import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussInvariance

namespace OAI

/-! The metric and intrinsic Gauss expression in phase coordinates are
fixed by the prescribed global metric, independently of its isometric
realization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseMetricRead (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base)
    (g : SmoothMetric M) (x : SmallModes.Base) : PhaseMean.Tensor :=
  tensorCoordinatePullbackValue T (baseEquiv.symm x)
    (A.tensorChartRead i g.inner (T (baseEquiv.symm x)))

lemma phaseMetricRead_smooth (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) (g : SmoothMetric M) : ContDiff ℝ ∞ (A.phaseMetricRead i T g) :=
  ((tensorCoordinatePullbackValue_smooth hT).clm_apply
    ((A.tensorChartRead_smooth i g.contMDiff).comp hT)).comp baseEquiv.symm.contDiff

lemma phaseMetricRead_isometry (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : JetPolynomial.Base}
    (hp : A.chartWeight i (T p) ≠ 0) :
    realMetricTensor (A.phaseRealChartMap i T F) (baseEquiv p) =
      A.phaseMetricRead i T g (baseEquiv p) := by
  have hm : g.inner = inducedTensor F := by
    funext q
    ext v w
    exact (hF.2 q v w).symm
  change realMetricTensor ((A.jetChartMap i F ∘ T) ∘ planeCoordinateIsometry.symm)
    (planeCoordinateIsometry p) = _
  rw [metric_coordinate_pullback (A.jetChartMap_smooth i hF.1) hT p,
    A.metric_read_on_weight i hF.1 hp,← hm]
  simp only [phaseMetricRead,baseEquiv.symm_apply_apply]

lemma phaseMetricRead_isometry_germ (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    realMetricTensor (A.phaseRealChartMap i T F) =ᶠ[𝓝 p] A.phaseMetricRead i T g := by
  have hc : Continuous (fun x : SmallModes.Base => A.chartWeight i (T (baseEquiv.symm x))) :=
    (A.chartWeight_smooth i).continuous.comp (hT.continuous.comp baseEquiv.symm.continuous)
  filter_upwards [((isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).preimage hc).mem_nhds hp] with x hx
  have hh := A.phaseMetricRead_isometry i hT hF (p := baseEquiv.symm x) hx
  rw [baseEquiv.apply_symm_apply] at hh
  exact hh

lemma phaseGauss_isometry (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    coordinateGauss (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dx)
      (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dy)
      (realMetric (A.phaseRealChartMap i T F) SmallModes.dy SmallModes.dy) p =
    coordinateGauss (fun x => A.phaseMetricRead i T g x 0)
      (fun x => A.phaseMetricRead i T g x 1) (fun x => A.phaseMetricRead i T g x 2) p := by
  have hg := A.phaseMetricRead_isometry_germ i hT hF hp
  apply coordinateGauss_germ
  · exact hg.mono (fun x hx => congrFun hx 0)
  · exact hg.mono (fun x hx => congrFun hx 1)
  · exact hg.mono (fun x hx => congrFun hx 2)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

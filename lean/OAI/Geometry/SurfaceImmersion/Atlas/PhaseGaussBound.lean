import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussBound

namespace OAI

/-! A compact curvature bound depends on the prescribed metric in the
phase chart, before choosing any oscillatory realization. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_phase_gauss_bound (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    (g : SmoothMetric M) {C : Set SmallModes.Base} (hC : IsCompact C)
    (hactive : ∀ x ∈ C, A.chartWeight i (T (baseEquiv.symm x)) ≠ 0)
    (hdet : ∀ x ∈ C, A.phaseMetricRead i T g x 0 * A.phaseMetricRead i T g x 2 -
      (A.phaseMetricRead i T g x 1)^2 ≠ 0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ F : M → Space, IsSmoothIsometricImmersion M g F → ∀ x ∈ C,
      |coordinateGauss (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dx)
        (realMetric (A.phaseRealChartMap i T F) SmallModes.dx SmallModes.dy)
        (realMetric (A.phaseRealChartMap i T F) SmallModes.dy SmallModes.dy) x| ≤ B := by
  have hm := A.phaseMetricRead_smooth i hT g
  have hc := coordinateGauss_continuousOn (contDiff_pi.mp hm 0) (contDiff_pi.mp hm 1)
    (contDiff_pi.mp hm 2) hdet
  obtain ⟨B,hB⟩ := (hC.image_of_continuousOn hc.abs).bddAbove
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro F hF x hx
  rw [A.phaseGauss_isometry i hT hF (hactive x hx)]
  exact (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

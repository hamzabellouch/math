import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Atlas.RealPhaseChart

namespace OAI

/-! Identifications of the actual surface phase chart in real coordinates. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseChart_real_apply (q p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    surfacePhaseChart q e p = ((coordinateChart q).trans (JetPolynomial.realPhaseChart e)) p := by
  change baseEquiv (e (FiniteOrderSmoothing.chart q p)) =
    baseEquiv
      (e (baseEquiv.symm (coordinateChart q p)))
  have hq : coordinateChart q p = baseEquiv (FiniteOrderSmoothing.chart q p) := rfl
  rw [hq,baseEquiv.symm_apply_apply]

lemma surfacePhaseChart_real_source (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    (surfacePhaseChart q e).source =
      ((coordinateChart q).trans (JetPolynomial.realPhaseChart e)).source := by
  ext p
  change (p ∈ (FiniteOrderSmoothing.chart q).source ∧
    FiniteOrderSmoothing.chart q p ∈ e.source) ↔
    (p ∈ (coordinateChart q).source ∧
      baseEquiv.symm (coordinateChart q p) ∈ e.source)
  have hq : coordinateChart q p = baseEquiv (FiniteOrderSmoothing.chart q p) := rfl
  rw [hq,baseEquiv.symm_apply_apply,FiniteOrderSmoothing.chart_source,coordinateChart_source]

end ClosedSurfaceR4

end

end OAI

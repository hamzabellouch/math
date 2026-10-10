import OAI.Geometry.SurfaceImmersion.Atlas.UniformCenteredCharts
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts

namespace OAI

/-! The whole-disk real phase charts in the coordinate representation used
by the nonlinear primitive construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes

def jetPhaseChart (e : OpenPartialHomeomorph Base Base) :
    OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base :=
  (baseEquiv.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph baseEquiv.symm.toHomeomorph

lemma jetPhaseChart_apply (e : OpenPartialHomeomorph Base Base) (x : JetPolynomial.Base) :
    jetPhaseChart e x = baseEquiv.symm (e (baseEquiv x)) := rfl

lemma jetPhaseChart_symm_apply (e : OpenPartialHomeomorph Base Base) (x : JetPolynomial.Base) :
    (jetPhaseChart e).symm x = baseEquiv.symm (e.symm (baseEquiv x)) := rfl

lemma jetPhaseChart_source (e : OpenPartialHomeomorph Base Base) :
    (jetPhaseChart e).source = baseEquiv ⁻¹' e.source := rfl

lemma jetPhaseChart_smooth {e : OpenPartialHomeomorph Base Base} (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (jetPhaseChart e) :=
  baseEquiv.symm.contDiff.comp (he.comp baseEquiv.contDiff)

lemma jetPhaseChart_symm_smooth {e : OpenPartialHomeomorph Base Base}
    (hi : ContDiff ℝ ∞ e.symm) : ContDiff ℝ ∞ (jetPhaseChart e).symm :=
  baseEquiv.symm.contDiff.comp (hi.comp baseEquiv.contDiff)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseChart_jetPhaseChart_apply (q p : M) (e : OpenPartialHomeomorph Base Base) :
    surfacePhaseChart q (jetPhaseChart e) p = e (coordinateChart q p) := by
  rw [surfacePhaseChart_apply,jetPhaseChart_apply,baseEquiv.apply_symm_apply]
  rfl

lemma surfacePhaseChart_jetPhaseChart_source (q : M) (e : OpenPartialHomeomorph Base Base) :
    (surfacePhaseChart q (jetPhaseChart e)).source =
      (coordinateChart q).source ∩ (coordinateChart q) ⁻¹' e.source := by
  ext p
  change (p ∈ (FiniteOrderSmoothing.chart q).source ∧
    baseEquiv (FiniteOrderSmoothing.chart q p) ∈ e.source) ↔ _
  rw [FiniteOrderSmoothing.chart_source,coordinateChart_source]
  rfl

end ClosedSurfaceR4

end

end OAI

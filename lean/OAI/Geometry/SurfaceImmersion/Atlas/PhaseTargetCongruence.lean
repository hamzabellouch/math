import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts

namespace OAI

/-! Restricting a target phase chart keeps every transition function. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseTransition_target_congr (p q r : M) (hqr : q = r)
    (e f g : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hfg : ∀ x, f x = g x) :
    (surfacePhaseTransition p e q f : SmallModes.Base → SmallModes.Base) =
      surfacePhaseTransition p e r g := by
  subst r
  funext x
  change baseEquiv (f (FiniteOrderSmoothing.chart q ((surfacePhaseChart p e).symm x))) =
    baseEquiv (g (FiniteOrderSmoothing.chart q ((surfacePhaseChart p e).symm x)))
  rw [hfg]

end ClosedSurfaceR4

end

end OAI

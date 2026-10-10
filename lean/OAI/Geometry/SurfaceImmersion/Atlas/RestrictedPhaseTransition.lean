import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionCocycle

namespace OAI

/-! Restricting the phase chart's source leaves its coordinate directions
unchanged on the original chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma same_phase_transition_fderiv (q r : M) (hqr : q = r)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hfe : ∀ x, f x = e x) {p : M} (hp : p ∈ (surfacePhaseChart q e).source) :
    fderiv ℝ (surfacePhaseTransition q e r f) (surfacePhaseChart q e p) =
      ContinuousLinearMap.id ℝ Base := by
  have hfun : (surfacePhaseTransition q e r f : Base → Base) = surfacePhaseTransition q e q e := by
    funext x
    change surfacePhaseChart r f ((surfacePhaseChart q e).symm x) =
      surfacePhaseChart q e ((surfacePhaseChart q e).symm x)
    simp only [surfacePhaseChart_apply,hfe,← hqr]
  rw [hfun]
  exact surfacePhaseTransition_self_fderiv q e ((surfacePhaseChart q e).map_source hp)

end ClosedSurfaceR4

end

end OAI

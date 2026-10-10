import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionCocycle

namespace OAI

/-! A phase-coordinate transition preserves nonzero tangent directions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma surfacePhaseTransition_fderiv_injective (p q : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {a : M} (hp : a ∈ (surfacePhaseChart p e).source)
    (hq : a ∈ (surfacePhaseChart q f).source) :
    Function.Injective (fderiv ℝ (surfacePhaseTransition p e q f) (surfacePhaseChart p e a)) := by
  have hh := surfacePhaseTransition_fderiv_cocycle p q p e f e hi hf hfi he hp hq hp
  rw [surfacePhaseTransition_self_fderiv p e ((surfacePhaseChart p e).map_source hp)] at hh
  intro v w hvw
  have hv := congrArg (fun L : Base →L[ℝ] Base => L v) hh
  have hw := congrArg (fun L : Base →L[ℝ] Base => L w) hh
  simp only [ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] at hv hw
  exact hv.trans ((congrArg (fderiv ℝ (surfacePhaseTransition q f p e)
    (surfacePhaseChart q f a)) hvw).trans hw.symm)

end ClosedSurfaceR4

end

end OAI

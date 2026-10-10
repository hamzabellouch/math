import OAI.Geometry.SurfaceImmersion.Atlas.ChartMapReplacement

namespace OAI

/-! Immersion of a smooth coordinate representative is equivalent to
immersion of the represented surface map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma chart_germ_immersion_iff (p : M) {q : M} (hq : q ∈ (chart p).source)
    {g : M → ProjectionTarget 3} {G : Base → ProjectionTarget 3}
    (hG : ContDiff ℝ ∞ G) (he : g =ᶠ[𝓝 q] G ∘ chart p) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g q) ↔
      Function.Injective (fderiv ℝ G (chart p q)) := by
  have hGc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,ProjectionTarget 3) ∞ G := hG.contMDiff
  rw [he.mfderiv_eq,mfderiv_comp q (hGc.mdifferentiable (by simp)).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt hq),mfderiv_eq_fderiv]
  change Function.Injective (fderiv ℝ G (chart p q) ∘
    mfderiv planeModel 𝓘(ℝ,Base) (chart p) q) ↔ _
  constructor
  · intro hi
    exact hi.of_comp_right ((chart_mdifferentiable p).mfderiv_surjective hq)
  · intro hi
    exact hi.comp ((chart_mdifferentiable p).mfderiv_injective hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

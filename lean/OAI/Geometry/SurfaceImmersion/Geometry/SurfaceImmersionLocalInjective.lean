import OAI.Geometry.SurfaceImmersion.Geometry.EuclideanImmersionLocalInjective
import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion

namespace OAI

/-! Actual regular surface points have neighborhoods on which the map is injective. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_immersion_locally_injective {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p : M) (hp : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  obtain ⟨U,F,hU,hpU,hUs,hF,heF⟩ := surface_chart_representative hf p
  have hpF := (chart_germ_immersion_iff p (hUs hpU) hF
    (heF.eventuallyEq_of_mem (hU.mem_nhds hpU))).mp hp
  obtain ⟨V,hV,hpV,hVinj⟩ := euclidean_immersion_locally_injective hF (chart p p) hpF
  refine ⟨U ∩ (chart p) ⁻¹' V,
    ((chart p).continuousOn.mono hUs).isOpen_inter_preimage hU hV,⟨hpU,hpV⟩,?_⟩
  intro x hx y hy heq
  apply (chart p).injOn (hUs hx.1) (hUs hy.1)
  apply hVinj hx.2 hy.2
  change (F ∘ chart p) x = (F ∘ chart p) y
  rw [← heF hx.1,← heF hy.1,heq]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

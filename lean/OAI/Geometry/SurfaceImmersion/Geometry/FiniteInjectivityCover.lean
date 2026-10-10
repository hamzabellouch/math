import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceInjectivityPatch

namespace OAI

/-! Finite quantitative injectivity cover of a compact immersed region. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem finite_injectivity_cover {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {B : Set M} (hB : IsCompact B)
    (hI : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
    ∃ (P : ∀ x : B, SurfaceInjectivityPatch f x.val) (s : Finset B),
      B ⊆ ⋃ x ∈ s, (P x).region := by
  classical
  let P : ∀ x : B, SurfaceInjectivityPatch f x.val := fun x =>
    Classical.choice (exists_surface_injectivity_patch hf x.val (hI x x.property))
  have hcover : B ⊆ ⋃ x : B, (P x).region :=
    fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,(P ⟨x,hx⟩).mem_region⟩
  obtain ⟨s,hs⟩ := hB.elim_finite_subcover (fun x => (P x).region)
    (fun x => (P x).region_open) hcover
  exact ⟨P,s,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

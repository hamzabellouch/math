import OAI.Geometry.SurfaceImmersion.Whitney.CleanSurfacePairs

namespace OAI

/-! Frozen translation germs preserve both clean coincidences and their regularity. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma FrozenTranslationGerms.clean_pair {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (S : Set M) (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i)
    (hclean : (x,y) ∈ cleanSurfacePairs f S) : (x,y) ∈ cleanSurfacePairs g S := by
  apply mem_cleanSurfacePairs.mpr
  intro heq
  have hh := (mem_cleanSurfacePairs.mp hclean) ((h.coincidence_iff i hx hy).mp heq)
  refine ⟨hh.1,hh.2.1,?_⟩
  rw [h.pairDerivative_eq hf i hx hy]
  exact hh.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

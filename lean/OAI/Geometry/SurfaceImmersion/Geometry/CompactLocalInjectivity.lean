import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic

namespace OAI

/-! A continuous map injective on a compact set and locally injective
near it is injective on some open neighborhood of the compact set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem compact_local_injectivity {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) (hi : K.InjOn f)
    (hloc : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U.InjOn f) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V.InjOn f := by
  classical
  let S := {U : Set X // IsOpen U ∧ U.InjOn f}
  let A : Set (X × X) := {z | f z.1 ≠ f z.2} ∪ ⋃ U : S, (U: Set X) ×ˢ (U: Set X)
  have hA : IsOpen A := (isOpen_ne_fun (hf.comp continuous_fst)
    (hf.comp continuous_snd)).union (isOpen_iUnion fun U => U.property.1.prod U.property.1)
  have hKA : K ×ˢ K ⊆ A := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases hxy : f x = f y
    · have heq := hi hx hy hxy
      change x = y at heq
      subst y
      obtain ⟨U,hU,hxU,hUi⟩ := hloc x hx
      exact Or.inr (mem_iUnion.mpr ⟨⟨U,hU,hUi⟩,hxU,hxU⟩)
    · exact Or.inl hxy
  obtain ⟨U,V,hU,hV,hKU,hKV,hUV⟩ := generalized_tube_lemma hK hK hA hKA
  refine ⟨U ∩ V,hU.inter hV,subset_inter hKU hKV,?_⟩
  intro x hx y hy hxy
  rcases hUV (show (x,y) ∈ U ×ˢ V from ⟨hx.1,hy.2⟩) with hn | hn
  · exact False.elim (hn hxy)
  · obtain ⟨W,hxW,hyW⟩ := mem_iUnion.mp hn
    exact W.property.2 hxW hyW hxy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

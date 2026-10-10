import OAI.Geometry.SurfaceImmersion.Whitney.UnorderedSurfacePairs

namespace OAI

/-! Away from the diagonal the quotient by interchanging the two points
is locally a homeomorphism, using disjoint coordinate neighborhoods. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem unordered_pair_local_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    (p q : M) (hpq : p ≠ q) :
    ∃ e : OpenPartialHomeomorph (M × M) (UnorderedSurfacePairs M),
      (p,q) ∈ e.source ∧ (∀ z, e z = unorderedPair z) ∧
      ∀ z ∈ e.source, z.1 ≠ z.2 := by
  have : Nonempty (M × M) := ⟨(p,q)⟩
  obtain ⟨U,V,hU,hV,hp,hq,hd⟩ := t2_separation hpq
  let E := (unorderedPair_injOn_product hd).toPartialEquiv unorderedPair (U ×ˢ V)
  let e := OpenPartialHomeomorph.ofContinuousOpen E unorderedPair_continuous.continuousOn
    unorderedPair_isOpenMap (hU.prod hV)
  refine ⟨e,⟨hp,hq⟩,(fun _ => rfl),?_⟩
  intro z hz heq
  exact Set.disjoint_left.mp hd hz.1 (heq ▸ hz.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

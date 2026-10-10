import OAI.Geometry.SurfaceImmersion.Whitney.CompactArcSubdivision
import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeWitness

namespace OAI

/-! A finite compact arc cover yields finitely many pairwise disjoint
connected open pieces after its finite vertices are deleted. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι]

theorem finite_arc_pieces (A : ι → CompactCurveArc X) (V : Set X) (hV : V.Finite)
    (hleft : ∀ i, (A i).map ⟨(A i).left,le_rfl,(A i).ordered.le⟩ ∈ V)
    (hright : ∀ i, (A i).map ⟨(A i).right,(A i).ordered.le,le_rfl⟩ ∈ V)
    (hcover : (univ : Set X) ⊆ ⋃ i, range (A i).map) :
    ∃ P : Finset (Set X),
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧
      Vᶜ = ⋃ E ∈ P, E ∧ (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) := by
  classical
  choose S hS hbound hlocal hp using fun i => subdivide_compact_arc (A i) V hV (hleft i) (hright i)
  let L (i : ι) := ((S i) ×ˢ (S i)).filter (fun uv => ConsecutiveVertices (S i) uv.1 uv.2)
  let P := Finset.univ.biUnion fun i => (L i).image (fun uv => (A i).openSubarc uv.1 uv.2)
  have hmem (E : Set X) : E ∈ P ↔ ∃ i u v,
      ConsecutiveVertices (S i) u v ∧ E = (A i).openSubarc u v := by
    constructor
    · intro he
      obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
      obtain ⟨uv,huv,heq⟩ := Finset.mem_image.mp hei
      exact ⟨i,uv.1,uv.2,(Finset.mem_filter.mp huv).2,heq.symm⟩
    · rintro ⟨i,u,v,huv,rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨(u,v),?_,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huv.1,huv.2.1⟩,huv⟩
  have hprop : ∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V := by
    intro E he
    obtain ⟨i,u,v,huv,rfl⟩ := (hmem E).mp he
    exact hp i u v huv
  refine ⟨P,hprop,?_,?_,?_⟩
  · intro E he F hf hne
    have eprop := hprop E he
    have fprop := hprop F hf
    exact (connected_open_pieces_equal_or_disjoint eprop.1 fprop.1
      eprop.2.1.isPreconnected fprop.2.1.isPreconnected eprop.2.2.2 fprop.2.2.2
      eprop.2.2.1 fprop.2.2.1).resolve_left hne
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover (mem_univ x))
      obtain ⟨u,v,huv,hxuv⟩ := hlocal i x hi hx
      exact mem_iUnion₂.mpr ⟨(A i).openSubarc u v,(hmem _).mpr ⟨i,u,v,huv,rfl⟩,hxuv⟩
    · intro x hx
      obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hx
      exact fun hxV => disjoint_left.mp (hprop E hE).2.2.1 hxE hxV

  · intro E he
    obtain ⟨i,u,v,huv,rfl⟩ := (hmem E).mp he
    have hu := hbound i u huv.1
    have hv := hbound i v huv.2.1
    exact ⟨⟨A i,u,v,hu.1,hv.2,huv.2.2.1,rfl,
      (hS i _).mp huv.1,(hS i _).mp huv.2.1⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

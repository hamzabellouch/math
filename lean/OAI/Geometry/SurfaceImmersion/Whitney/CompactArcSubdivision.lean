import OAI.Geometry.SurfaceImmersion.Whitney.ArcVertexCoordinates
import OAI.Geometry.SurfaceImmersion.Geometry.ConnectedOpenPieces

namespace OAI

/-! Subdivide a compact embedded arc at every prescribed finite vertex.
The resulting pieces are connected open sets with frontier in that set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem subdivide_compact_arc (A : CompactCurveArc X) (V : Set X) (hV : V.Finite)
    (hleft : A.map ⟨A.left,le_rfl,A.ordered.le⟩ ∈ V)
    (hright : A.map ⟨A.right,A.ordered.le,le_rfl⟩ ∈ V) :
    ∃ S : Finset ℝ,
      (∀ t : Icc A.left A.right, (t:ℝ) ∈ S ↔ A.map t ∈ V) ∧
      (∀ r ∈ S, A.left ≤ r ∧ r ≤ A.right) ∧
      (∀ x ∈ range A.map, x ∉ V → ∃ u v,
        ConsecutiveVertices S u v ∧ x ∈ A.openSubarc u v) ∧
      ∀ u v, ConsecutiveVertices S u v →
        IsOpen (A.openSubarc u v) ∧ IsConnected (A.openSubarc u v) ∧
        Disjoint (A.openSubarc u v) V ∧ closure (A.openSubarc u v) \ A.openSubarc u v ⊆ V := by
  classical
  obtain ⟨S,hS,hbound⟩ := arc_vertex_coordinates A V hV
  have hlS : A.left ∈ S := (hS ⟨A.left,le_rfl,A.ordered.le⟩).mpr hleft
  have hrS : A.right ∈ S := (hS ⟨A.right,A.ordered.le,le_rfl⟩).mpr hright
  refine ⟨S,hS,hbound,?_,?_⟩
  · rintro x ⟨t,rfl⟩ hx
    have htS : (t:ℝ) ∉ S := fun ht => hx ((hS t).mp ht)
    have hlt : A.left < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun h => htS (h ▸ hlS))
    have htr : (t:ℝ) < A.right := lt_of_le_of_ne t.property.2 (fun h => htS (h.symm ▸ hrS))
    obtain ⟨u,v,huv,hu,hv⟩ := exists_consecutive_interval S htS ⟨A.left,hlS,hlt⟩ ⟨A.right,hrS,htr⟩
    exact ⟨u,v,huv,t,⟨hu,hv⟩,rfl⟩
  · intro u v huv
    have hu := hbound u huv.1
    have hv := hbound v huv.2.1
    have hne := huv.2.2.1
    have huV : A.map ⟨u,hu⟩ ∈ V := (hS ⟨u,hu⟩).mp huv.1
    have hvV : A.map ⟨v,hv⟩ ∈ V := (hS ⟨v,hv⟩).mp huv.2.1
    refine ⟨A.openSubarc_open hu.1 hv.2,A.subarc_connected hu.1 hv.2 hne,?_,?_⟩
    · apply disjoint_left.mpr
      rintro x ⟨t,ht,rfl⟩ hxV
      exact huv.2.2.2 t ((hS t).mpr hxV) ht
    · intro x hx
      rcases A.subarc_frontier hu.1 hv.2 hne hx.1 hx.2 with he | he
      · exact he ▸ huV
      · exact he ▸ hvV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

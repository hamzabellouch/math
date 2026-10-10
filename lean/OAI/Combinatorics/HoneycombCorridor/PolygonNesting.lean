import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Traversals

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor
namespace Polygon

theorem boundary_zero_face (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    ∃ k : Fin 3, P.potential (leftFace (v,k)) = 0 := by
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  have hloc := (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1
  by_contra hn
  push Not at hn
  have hzero (l : Fin 3) : orientedFlow (wordFlow P.germ P.turns) (v,l) = 0 := by
    rw [P.represents (v,l),rightFace_prev]
    have h1 := (P.potential_spec.2.2.2 (leftFace (v,l))).resolve_left (hn l)
    have h2 := (P.potential_spec.2.2.2 (leftFace (v,l+2))).resolve_left (hn (l+2))
    rw [h1,h2,sub_self]
  have hs : edgeOf (v,k) ∈ (wordFlow (v,k) (b :: u)).support :=
    (local_contour_support _ (v,k) b hloc k).mpr (Or.inl rfl)
  rw [hw.2.2.2,← P.traversal.2.2.2,Finsupp.mem_support_iff] at hs
  exact hs ((orientedFlow_zero_iff _ _).mp (hzero k))

theorem interiorFaces_subset (P Q : Polygon) (hQ : Q.vertices ⊆ P.interior) :
    Q.interiorFaces ⊆ P.interiorFaces := by
  have hedge (e : EdgeIndex) (he : e ∈ Q.val) : e ∈ cellEdges P.interiorFaces := by
    have hvQ : upEnd e ∈ Q.vertices := Finset.mem_biUnion.mpr ⟨e,he,by simp⟩
    have hv := (P.interior_iff_level _).mp (hQ hvQ)
    have hl : P.potential (leftFace (canonicalDart e)) ≠ 0 := by
      rw [show canonicalDart e = (upEnd e,e.2) from rfl,
        (P.off_boundary_faces _ hv.1 e.2).1]
      exact hv.2
    exact (mem_cellEdges _ e).mpr (Or.inl (Finsupp.mem_support_iff.mpr hl))
  have h := potential_supported_on_cycle_cells P.germ P.turns
    P.traversal.2.1 P.traversal.2.2.1 P.potential P.represents P.potential_spec.2.1
    (toRatFinsupp Q.potential) (by
      intro e he
      rw [Q.represents.rational,toRatFinsupp_apply]
      have hz : wordFlow Q.germ Q.turns e = 0 := by
        by_contra hn
        exact he (hedge e (by rw [← Q.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn))
      simp [hz])
  simpa only [toRatFinsupp_support,interiorFaces] using h

theorem interior_subset (P Q : Polygon) (hQ : Q.vertices ⊆ P.interior) :
    Q.interior ⊆ P.interior := by
  have hfaces := P.interiorFaces_subset Q hQ
  intro v hv
  have hq := (Q.interior_iff_level v).mp hv
  have hall (k : Fin 3) : P.potential (leftFace (v,k)) ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    apply hfaces
    apply Finsupp.mem_support_iff.mpr
    rw [(Q.off_boundary_faces v hq.1 k).1]
    exact hq.2
  apply (P.interior_iff_level v).mpr
  constructor
  · intro hb
    obtain ⟨k,hk⟩ := P.boundary_zero_face v hb
    exact hall k hk
  · exact hall 0

theorem interior_filled (P : Polygon) : Filled P.interior := by
  intro Q hQ
  exact P.interior_subset Q ((mem_polygons _ _).mp hQ)

theorem vertices_nonempty (P : Polygon) : P.vertices.Nonempty := by
  rw [P.vertices_traversal]
  obtain ⟨head,tail,hturns⟩ := List.exists_cons_of_ne_nil P.traversal.1
  exact ⟨P.germ.1,by simp [hturns,traced]⟩

theorem interior_card_lt (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) : P.interior.card < D.card := by
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hD P hP,?_⟩
  intro he
  have hvD := (mem_polygons D P).mp hP hv
  rw [← he] at hvD
  exact ((P.mem_interior v).mp hvD).2 hv

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI

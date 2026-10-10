import OAI.Combinatorics.PolynomialVacuum.Cylinder.PolygonMinimality

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem disjoint_polygons_eq_of_mem (S : Finset (Polygon M))
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    {P Q : Polygon M} (hP : P∈S) (hQ : Q∈S) {v : Vertex M}
    (hvP : v∈P.vertices) (hvQ : v∈Q.vertices) : P=Q := by
  by_contra hn
  exact Finset.disjoint_left.mp (hS hP hQ hn) hvP hvQ

theorem word_edges_in_one_polygon (S : Finset (Polygon M))
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (Q : Polygon M) (hQ : Q∈S) (g : Germ M) (w : List Bool)
    (hs : tracedEdges g w⊆S.biUnion Subtype.val) (hg : g.1∈Q.vertices) :
    tracedEdges g w⊆Q.val := by
  induction w generalizing g with
  | nil => simp [tracedEdges]
  | cons b w ih =>
    have he:=hs (Finset.mem_insert_self (edgeOf (g.1,outgoingSlot g b)) (tracedEdges (advance g b) w))
    obtain ⟨P,hP,he⟩:=Finset.mem_biUnion.mp he
    have hp:=edge_vertices_subset_polygon P _ he
    have hPQ : P=Q := disjoint_polygons_eq_of_mem S hS hP hQ (hp (by simp)) hg
    subst P
    apply Finset.insert_subset_iff.mpr
    refine ⟨he,ih (advance g b) (fun e he => hs (Finset.mem_insert_of_mem he)) ?_⟩
    apply hp
    change neighbor g.1 (outgoingSlot g b)∈edgeVertices (edgeOf (g.1,outgoingSlot g b))
    simp only [edgeVertices_edgeOf,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

theorem polygon_mem_of_covered (S : Finset (Polygon M))
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (P : Polygon M) (h : P.val⊆S.biUnion Subtype.val) : P∈S := by
  obtain ⟨hne,_,_,he⟩:=polygon_witness P
  obtain ⟨b,w,hw⟩:=List.exists_cons_of_ne_nil hne
  have ht : tracedEdges (polygonGerm P) (polygonWord P)⊆S.biUnion Subtype.val := by rw [he]; exact h
  have hed : edgeOf ((polygonGerm P).1,outgoingSlot (polygonGerm P) b)∈P.val := by
    rw [← he,hw,tracedEdges]
    simp
  obtain ⟨Q,hQ,heQ⟩:=Finset.mem_biUnion.mp (h hed)
  have hg : (polygonGerm P).1∈Q.vertices:=edge_vertices_subset_polygon Q _ heQ (by simp)
  have hh:=word_edges_in_one_polygon S hS Q hQ (polygonGerm P) (polygonWord P) ht hg
  rw [he] at hh
  exact polygon_eq_of_subset P Q hh ▸ hQ

theorem polygon_system_eq_of_edge_union (S T : Finset (Polygon M))
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (hT : (T : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (h : S.biUnion Subtype.val=T.biUnion Subtype.val) : S=T := by
  apply Finset.Subset.antisymm
  · intro P hP
    apply polygon_mem_of_covered T hT P
    intro e he
    rw [← h]
    exact Finset.mem_biUnion.mpr ⟨P,hP,he⟩
  · intro P hP
    apply polygon_mem_of_covered S hS P
    intro e he
    rw [h]
    exact Finset.mem_biUnion.mpr ⟨P,hP,he⟩

theorem systemCurrent_polygons (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    (IceNetwork.network (systemCurrent S o) (systemCurrent_localIce S o hS)).polygons=S := by
  let C:=IceNetwork.network (systemCurrent S o) (systemCurrent_localIce S o hS)
  apply polygon_system_eq_of_edge_union C.polygons S C.polygons_disjoint hS
  obtain ⟨p,hp⟩:=ice_current_orientation_decomposition (systemCurrent S o) (systemCurrent_localIce S o hS)
  have hs:=congrArg Finsupp.support hp
  rw [systemCurrent_support S o hS,systemCurrent_support _ p C.polygons_disjoint] at hs
  exact hs.symm

end PolynomialVacuumCylinder

end OAI

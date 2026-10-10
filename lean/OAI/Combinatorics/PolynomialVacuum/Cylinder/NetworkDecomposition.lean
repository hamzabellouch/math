import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkVertices

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
namespace ClosedNetwork
variable {M : ℕ} (C : ClosedNetwork M)

noncomputable def outEdge (v : C.sites) : Edge M := edgeOf (v.val,C.exit v)

theorem mem_word_edges (k : ℕ) (v : C.sites) (e : Edge M) :
    e∈tracedEdges (C.germ v) (C.word k v) ↔ ∃ j<k,C.outEdge (C.next^[j] v)=e := by
  induction k generalizing v with
  | zero => simp [word,tracedEdges]
  | succ k ih =>
    simp only [word,tracedEdges,C.advance_turn,C.outgoing_turn,Finset.mem_insert]
    rw [ih]
    constructor
    · rintro (he | ⟨j,hj,he⟩)
      · exact ⟨0,by omega,he.symm⟩
      · exact ⟨j+1,by omega,by simpa only [Function.iterate_succ_apply] using he⟩
    · rintro ⟨j,hj,he⟩
      cases j with
      | zero => exact Or.inl he.symm
      | succ j => exact Or.inr ⟨j,by omega,he⟩

theorem mem_polygon_edges (v : C.sites) (e : Edge M) :
    e∈(C.polygon v).val ↔ ∃ u : C.sites,u.val∈(C.polygon v).vertices ∧ C.outEdge u=e := by
  change e∈tracedEdges (C.germ v) (C.word (C.period v) v) ↔ _
  rw [C.mem_word_edges]
  constructor
  · rintro ⟨j,hj,he⟩
    refine ⟨C.next^[j] v,?_,he⟩
    rw [C.polygon_vertices]
    exact Finset.mem_image.mpr ⟨j,by simpa using hj,rfl⟩
  · rintro ⟨u,hu,he⟩
    rw [C.polygon_vertices] at hu
    obtain ⟨j,hj,he'⟩:=Finset.mem_image.mp hu
    exact ⟨j,by simpa using hj,by rw [show C.next^[j] v=u from Subtype.ext he',he]⟩

theorem polygon_eq_of_sameCycle (v u : C.sites) (h : C.next.SameCycle v u) :
    C.polygon v=C.polygon u := by
  apply Subtype.ext
  ext e
  simp only [C.mem_polygon_edges,C.mem_polygon_vertices]
  constructor
  · rintro ⟨w,hw,he⟩; exact ⟨w,h.symm.trans hw,he⟩
  · rintro ⟨w,hw,he⟩; exact ⟨w,h.trans hw,he⟩

theorem polygon_eq_of_overlap (v u : C.sites) (x : Vertex M)
    (hv : x∈(C.polygon v).vertices) (hu : x∈(C.polygon u).vertices) : C.polygon v=C.polygon u := by
  let w : C.sites:=⟨x,C.polygon_vertices_subset v hv⟩
  have h1:= (C.mem_polygon_vertices v w).mp hv
  have h2:= (C.mem_polygon_vertices u w).mp hu
  exact C.polygon_eq_of_sameCycle v u (h1.trans h2.symm)

 

noncomputable def polygons : Finset (Polygon M) := Finset.univ.image C.polygon

theorem polygons_disjoint : (C.polygons : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices) := by
  intro P hP Q hQ hne
  obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hP
  obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hQ
  apply Finset.disjoint_left.mpr
  intro x hv hu
  exact hne (C.polygon_eq_of_overlap v u x hv hu)

theorem polygons_vertices : C.polygons.biUnion Polygon.vertices=C.sites := by
  ext x
  constructor
  · intro hx
    obtain ⟨P,hP,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hP
    exact C.polygon_vertices_subset v hx
  · intro hx
    let v : C.sites:=⟨x,hx⟩
    exact Finset.mem_biUnion.mpr ⟨C.polygon v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,
      (C.mem_polygon_vertices v v).mpr (Equiv.Perm.SameCycle.refl _ _)⟩

theorem polygons_edges : C.polygons.biUnion Subtype.val=Finset.univ.image C.outEdge := by
  ext e
  constructor
  · intro he
    obtain ⟨P,hP,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hP
    obtain ⟨u,_,hu⟩:=(C.mem_polygon_edges v e).mp he
    exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,hu⟩
  · rintro he
    obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp he
    refine Finset.mem_biUnion.mpr ⟨C.polygon u,Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩,?_⟩
    apply (C.mem_polygon_edges u _).mpr
    exact ⟨u,(C.mem_polygon_vertices u u).mpr (Equiv.Perm.SameCycle.refl _ _),rfl⟩

theorem polygons_total_length : (∑ P∈C.polygons,P.vertices.card)=C.sites.card := by
  rw [← C.polygons_vertices,Finset.card_biUnion]
  exact C.polygons_disjoint

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI

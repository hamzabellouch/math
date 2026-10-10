import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedCancellation

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

noncomputable def incidentEdges (D : Finset (Vertex M)) : Finset (Edge M) :=
  D.biUnion (fun v => Finset.univ.image (fun k : Fin 3 => edgeOf (v,k)))
noncomputable def internalEdges (D : Finset (Vertex M)) : Finset (Edge M) :=
  (incidentEdges D).filter (fun e => edgeVertices e⊆D)

theorem mem_incidentEdges_iff (D : Finset (Vertex M)) (e : Edge M) :
    e∈incidentEdges D ↔ ∃v∈D,v∈edgeVertices e := by
  rcases e with ⟨⟨i,j⟩,s⟩
  constructor
  · intro he
    obtain ⟨v,hv,h⟩:=Finset.mem_biUnion.mp he
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp h
    refine ⟨v,hv,?_⟩
    rw [← hk]
    simp
  · rintro ⟨v,hv,hve⟩
    simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hve
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,?_⟩⟩
    rcases hve with rfl | rfl
    · rfl
    · change edgeOf (reverseGerm (.up i j,s))=_
      rw [edgeOf_reverse]
      rfl

theorem support_internal_iff (q : Edge M →₀ ℤ) (D : Finset (Vertex M)) :
    q.support⊆internalEdges D ↔ activeSites q⊆D := by
  rw [activeSites_eq_support_vertices]
  constructor
  · intro hs v hv
    obtain ⟨e,he,hv⟩:=Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp (hs he)).2 hv
  · intro hv e he
    have hp : edgeVertices e⊆D := fun v hh => hv (Finset.mem_biUnion.mpr ⟨e,he,hh⟩)
    apply Finset.mem_filter.mpr
    refine ⟨(mem_incidentEdges_iff D e).mpr ?_,hp⟩
    refine ⟨.up e.1.1 e.1.2,hp (by simp [edgeVertices]),by simp [edgeVertices]⟩

abbrev ClosedDomainFlow (D : Finset (Vertex M)) := {q : LegalFlow M // activeSites q.val⊆D}
noncomputable def closedDomainEquiv (D : Finset (Vertex M)) :
    BoundedFlow (internalEdges D) ≃ ClosedDomainFlow D where
  toFun q:=⟨q.val,(support_internal_iff q.val.val D).mp q.property⟩
  invFun q:=⟨q.val,(support_internal_iff q.val.val D).mpr q.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
noncomputable instance (D : Finset (Vertex M)) : Fintype (ClosedDomainFlow D) :=
  Fintype.ofEquiv _ (closedDomainEquiv D)

 

theorem closed_domain_partition_one [NeZero M] (D : Finset (Vertex M)) :
    (∑q : ClosedDomainFlow D,uniformSeamWeight q.val.val)=1 := by
  rw [← (closedDomainEquiv D).sum_comp]
  exact uniform_closed_partition_one (internalEdges D)

end PolynomialVacuumCylinder

end OAI

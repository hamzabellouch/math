import OAI.Combinatorics.PolynomialVacuum.Cylinder.Translation
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedDomain

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

noncomputable def verticalSystem (y : ℤ) (S : DisjointSystem M) : DisjointSystem M :=
  ⟨S.val.image (verticalPolygon y),by
    intro P hP Q hQ hne
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hQ
    have hd:=S.property hp hq (fun he=>hne (congrArg (verticalPolygon y) he))
    rw [verticalPolygon_vertices,verticalPolygon_vertices]
    apply Finset.disjoint_left.mpr
    intro v hvp hvq
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hvp
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hvq
    have hba : b=a:=translate_injective 0 y he
    exact (Finset.disjoint_left.mp hd) ha (hba ▸ hb)⟩

@[simp] theorem verticalSystem_comp (x y : ℤ) (S : DisjointSystem M) :
    verticalSystem x (verticalSystem y S)=verticalSystem (y+x) S := by
  apply Subtype.ext
  simp only [verticalSystem,Finset.image_image]
  congr 1
  funext P
  exact verticalPolygon_comp x y P
@[simp] theorem verticalSystem_zero (S : DisjointSystem M) : verticalSystem 0 S=S := by
  apply Subtype.ext
  simp only [verticalSystem]
  have hh : verticalPolygon (M:=M) 0=id := funext verticalPolygon_zero
  rw [hh,Finset.image_id]

noncomputable def verticalSystemEquiv (y : ℤ) : DisjointSystem M ≃ DisjointSystem M where
  toFun:=verticalSystem y
  invFun:=verticalSystem (-y)
  left_inv S:=by simp
  right_inv S:=by simp

theorem verticalSystem_bound (y : ℤ) (S : DisjointSystem M) (E : Finset (Edge M)) :
    (∀P∈(verticalSystem y S).val,P.val⊆E.image (verticalEdge y)) ↔ ∀P∈S.val,P.val⊆E := by
  simp only [verticalSystem,Finset.forall_mem_image,verticalPolygon]
  have hi : Function.Injective (verticalEdge (M:=M) y):=(verticalEdgeEquiv y).injective
  simp only [Finset.image_subset_image_iff hi]

noncomputable def verticalBoundedEquiv (y : ℤ) (E : Finset (Edge M)) :
    BoundedSystem E ≃ BoundedSystem (E.image (verticalEdge y)) :=
  (verticalSystemEquiv y).subtypeEquiv (fun S=>(verticalSystem_bound y S E).symm)

theorem verticalSystem_separates (y : ℤ) (S : DisjointSystem M) (a b : Face M) :
    (∀P∈(verticalSystem y S).val,Separates P (verticalFace y a) (verticalFace y b)) ↔
      ∀P∈S.val,Separates P a b := by
  simp only [verticalSystem,Finset.forall_mem_image,vertical_separates]

theorem verticalSystem_card (y : ℤ) (S : DisjointSystem M) :
    (verticalSystem y S).val.card=S.val.card :=
  Finset.card_image_of_injective _ (verticalPolygonEquiv y).injective

theorem verticalSystem_length (y : ℤ) (S : DisjointSystem M) :
    (∑P∈(verticalSystem y S).val,P.vertices.card)=∑P∈S.val,P.vertices.card := by
  simp only [verticalSystem]
  have hi : Function.Injective (verticalPolygon (M:=M) y):=(verticalPolygonEquiv y).injective
  rw [Finset.sum_image (fun _ _ _ _ h=>hi h)]
  apply Finset.sum_congr rfl
  intro P _
  rw [verticalPolygon_vertices,Finset.card_image_of_injective _ (translate_injective 0 y)]

 
noncomputable def centeredEdges (M H : ℕ) [NeZero M] : Finset (Edge M) :=
  (internalEdges (bandSites M (H+(H+1)))).image (verticalEdge (-(H : ℤ)))

theorem mem_internalEdges (D : Finset (Vertex M)) (e : Edge M) :
    e∈internalEdges D ↔ edgeVertices e⊆D := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨(mem_incidentEdges_iff D e).mpr
      ⟨.up e.1.1 e.1.2,h (by simp [edgeVertices]),by simp [edgeVertices]⟩,h⟩

theorem mem_centeredEdges [NeZero M] (H : ℕ) (e : Edge M) :
    e∈centeredEdges M H ↔ ∀v∈edgeVertices e,-(H : ℤ)≤vertexLayer v ∧ vertexLayer v≤H := by
  have htrans : verticalEdge (-(H : ℤ)) (verticalEdge H e)=e :=
    (verticalEdgeEquiv (M:=M) (H : ℤ)).left_inv e
  have hinj : Function.Injective (verticalEdge (M:=M) (-(H : ℤ))):=(verticalEdgeEquiv _).injective
  have he : e∈centeredEdges M H ↔ verticalEdge H e∈internalEdges (bandSites M (H+(H+1))) := by
    rw [centeredEdges,Finset.mem_image]
    conv_lhs => rw [← htrans]
    simp only [hinj.eq_iff,exists_eq_right]
  rw [he,mem_internalEdges,vertical_edgeVertices,Finset.image_subset_iff]
  simp only [mem_bandSites,InBand,translate_layer]
  constructor <;> intro hh v hv <;> have hh:=hh v hv <;> omega

 theorem centeredEdges_mono [NeZero M] : Monotone (fun H=>centeredEdges M H) := by
  intro H K hHK e he
  rw [mem_centeredEdges] at he ⊢
  intro v hv
  have hh:=he v hv
  omega

 theorem eventually_mem_centeredEdges [NeZero M] (e : Edge M) :
    ∀ᶠ H : ℕ in Filter.atTop,e∈centeredEdges M H := by
  apply Filter.eventually_atTop.mpr
  obtain ⟨K,hK⟩:=Finset.exists_nat_subset_range ((edgeVertices e).image (fun v=>(vertexLayer v).natAbs))
  refine ⟨K,fun H hH=>?_⟩
  rw [mem_centeredEdges]
  intro v hv
  have hh:=Finset.mem_range.mp (hK (Finset.mem_image_of_mem _ hv))
  have ha:=Int.natCast_natAbs (vertexLayer v)
  have hab:=le_abs_self (vertexLayer v)
  have hal:=neg_abs_le (vertexLayer v)
  omega

end PolynomialVacuumCylinder

end OAI

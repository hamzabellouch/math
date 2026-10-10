import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcIsometries

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

def verticalFace (y : ℤ) (a : Face M) : Face M := (a.1,a.2+y)
def verticalEdge (y : ℤ) (e : Edge M) : Edge M := (verticalFace y e.1,e.2)

def verticalEdgeEquiv (y : ℤ) : Edge M ≃ Edge M where
  toFun:=verticalEdge y
  invFun:=verticalEdge (-y)
  left_inv e:=by rcases e with ⟨⟨i,j⟩,s⟩; simp [verticalEdge,verticalFace]
  right_inv e:=by rcases e with ⟨⟨i,j⟩,s⟩; simp [verticalEdge,verticalFace]

def verticalFaceEquiv (y : ℤ) : Face M ≃ Face M where
  toFun:=verticalFace y
  invFun:=verticalFace (-y)
  left_inv e:=by rcases e with ⟨i,j⟩; simp [verticalFace]
  right_inv e:=by rcases e with ⟨i,j⟩; simp [verticalFace]

@[simp] theorem vertical_edgeOf (y : ℤ) (g : Germ M) :
    edgeOf (mapGerm (translate 0 y) g)=verticalEdge y (edgeOf g) := by
  rcases g with ⟨v,s⟩
  cases v <;> fin_cases s <;> simp [edgeOf,mapGerm,translate,verticalEdge,verticalFace]; omega

@[simp] theorem vertical_leftFace (y : ℤ) (g : Germ M) :
    leftFace (mapGerm (translate 0 y) g)=verticalFace y (leftFace g) := by
  rcases g with ⟨v,s⟩
  cases v <;> fin_cases s <;> simp [leftFace,mapGerm,translate,verticalFace] <;> omega

@[simp] theorem vertical_reverse (y : ℤ) (g : Germ M) :
    reverseGerm (mapGerm (translate 0 y) g)=mapGerm (translate 0 y) (reverseGerm g) := by
  simp [reverseGerm,mapGerm]

@[simp] theorem vertical_rightFace (y : ℤ) (g : Germ M) :
    rightFace (mapGerm (translate 0 y) g)=verticalFace y (rightFace g) := by
  simp [rightFace]

theorem vertical_tracedEdges (y : ℤ) (g : Germ M) (w : List Bool) :
    tracedEdges (mapGerm (translate 0 y) g) w=(tracedEdges g w).image (verticalEdge y) := by
  induction w generalizing g with
  | nil => simp [tracedEdges]
  | cons b w ih =>
    rw [tracedEdges,tracedEdges,Finset.image_insert]
    have he : edgeOf ((mapGerm (translate 0 y) g).1,outgoingSlot (mapGerm (translate 0 y) g) b)=
        verticalEdge y (edgeOf (g.1,outgoingSlot g b)) := by
      simpa only [mapGerm,outgoingSlot] using vertical_edgeOf y (g.1,outgoingSlot g b)
    rw [he,← map_advance _ (translate_neighbor_cyl 0 y),ih]

theorem vertical_isPolygon (y : ℤ) (P : Polygon M) :
    IsPolygon (P.val.image (verticalEdge y)) := by
  obtain ⟨g,w,hw,hn,hc,he⟩:=P.property
  refine ⟨mapGerm (translate 0 y) g,w,hw,?_,?_,?_⟩
  · rw [← map_traced _ (translate_neighbor_cyl 0 y)]
    exact hn.map (translate_injective 0 y)
  · rw [← map_terminal _ (translate_neighbor_cyl 0 y),hc]
  · rw [vertical_tracedEdges,he]

noncomputable def verticalPolygon (y : ℤ) (P : Polygon M) : Polygon M :=
  ⟨P.val.image (verticalEdge y),vertical_isPolygon y P⟩

@[simp] theorem verticalPolygon_comp (x y : ℤ) (P : Polygon M) :
    verticalPolygon x (verticalPolygon y P)=verticalPolygon (y+x) P := by
  apply Subtype.ext
  simp only [verticalPolygon,Finset.image_image]
  congr 1
  funext e
  rcases e with ⟨⟨i,j⟩,s⟩
  simp [verticalEdge,verticalFace,add_assoc]
@[simp] theorem verticalPolygon_zero (P : Polygon M) : verticalPolygon 0 P=P := by
  apply Subtype.ext
  have hz : verticalEdge (M:=M) 0 = id := by
    funext e; rcases e with ⟨⟨i,j⟩,s⟩; simp [verticalEdge,verticalFace]
  simp only [verticalPolygon,hz,Finset.image_id]

noncomputable def verticalPolygonEquiv (y : ℤ) : Polygon M ≃ Polygon M where
  toFun:=verticalPolygon y
  invFun:=verticalPolygon (-y)
  left_inv P:=by simp
  right_inv P:=by simp

theorem vertical_edgeVertices (y : ℤ) (e : Edge M) :
    edgeVertices (verticalEdge y e)=(edgeVertices e).image (translate 0 y) := by
  rcases e with ⟨⟨i,j⟩,s⟩
  simp only [edgeVertices,Finset.image_insert,Finset.image_singleton]
  have h:=translate_neighbor_cyl 0 y (.up i j) s
  simpa [verticalEdge,verticalFace,translate] using congrArg (fun v=>({Vertex.up i (j+y),v} : Finset (Vertex M))) h.symm

theorem verticalPolygon_vertices (y : ℤ) (P : Polygon M) :
    (verticalPolygon y P).vertices=P.vertices.image (translate 0 y) := by
  simp only [Polygon.vertices,verticalPolygon,Finset.biUnion_image,vertical_edgeVertices,Finset.image_biUnion]

theorem vertical_dualAdjacent (y : ℤ) (E : Finset (Edge M)) (a b : Face M) :
    DualAdjacent (E.image (verticalEdge y)) (verticalFace y a) (verticalFace y b) ↔ DualAdjacent E a b := by
  constructor
  · rintro ⟨e,he,h⟩
    obtain ⟨e,rfl⟩:=(verticalEdgeEquiv (M:=M) y).surjective e
    have hn : e∉E := by intro hh; exact he (Finset.mem_image_of_mem _ hh)
    refine ⟨e,hn,?_⟩
    have hg : (.up (verticalEdge y e).1.1 (verticalEdge y e).1.2,(verticalEdge y e).2)=
        mapGerm (translate 0 y) (.up e.1.1 e.1.2,e.2) := by simp [verticalEdge,verticalFace,mapGerm,translate]
    dsimp only [verticalEdgeEquiv,Equiv.coe_fn_mk] at h
    rw [hg,vertical_leftFace,vertical_rightFace] at h
    have hi : Function.Injective (verticalFace (M:=M) y) := (verticalFaceEquiv y).injective
    simpa only [hi.eq_iff] using h
  · rintro ⟨e,he,h⟩
    refine ⟨verticalEdge y e,?_,?_⟩
    · intro hh
      obtain ⟨e',he',heq⟩:=Finset.mem_image.mp hh
      have hEq : e'=e := (verticalEdgeEquiv (M:=M) y).injective heq
      exact he (hEq ▸ he')
    · have hg : (.up (verticalEdge y e).1.1 (verticalEdge y e).1.2,(verticalEdge y e).2)=
          mapGerm (translate 0 y) (.up e.1.1 e.1.2,e.2) := by simp [verticalEdge,verticalFace,mapGerm,translate]
      rw [hg,vertical_leftFace,vertical_rightFace]
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩

theorem vertical_separates (y : ℤ) (P : Polygon M) (a b : Face M) :
    Separates (verticalPolygon y P) (verticalFace y a) (verticalFace y b) ↔ Separates P a b := by
  have hh : Relation.ReflTransGen (DualAdjacent (verticalPolygon y P).val) (verticalFace y a) (verticalFace y b) ↔
      Relation.ReflTransGen (DualAdjacent P.val) a b := by
    constructor
    · intro h
      have hm : Relation.ReflTransGen (DualAdjacent P.val)
          (verticalFace (-y) (verticalFace y a)) (verticalFace (-y) (verticalFace y b)) :=
        Relation.ReflTransGen.lift (verticalFace (-y)) (by
        intro x z hx
        obtain ⟨x,rfl⟩:=(verticalFaceEquiv (M:=M) y).surjective x
        obtain ⟨z,rfl⟩:=(verticalFaceEquiv (M:=M) y).surjective z
        simpa only [verticalFaceEquiv,Equiv.coe_fn_mk,verticalFace,add_neg_cancel_right,Function.onFun] using
          (vertical_dualAdjacent y P.val x z).mp hx) _ _ h
      simpa [verticalFace] using hm
    · intro h
      exact Relation.ReflTransGen.lift (verticalFace y) (fun x z hx=>(vertical_dualAdjacent y P.val x z).mpr hx) _ _ h
  exact not_congr hh

end PolynomialVacuumCylinder

end OAI

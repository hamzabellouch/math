import OAI.Combinatorics.PolynomialVacuum.Geometry.PolygonLaminar

namespace OAI

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem mem_polygonSystems (D : Finset Vertex) (f : FaceIndex) (S : Finset Polygon) :
    S ∈ polygonSystems D f ↔ S ⊆ polygons D ∧
      (S : Set Polygon).Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      ∀ P ∈ S, f ∈ P.interiorFaces := by
  classical
  simp only [polygonSystems,Finset.mem_filter,Finset.mem_powerset]

@[simp] theorem empty_mem_polygonSystems (D : Finset Vertex) (f : FaceIndex) :
    ∅ ∈ polygonSystems D f := by
  simp [mem_polygonSystems,Set.Pairwise]

theorem Polygon.not_vertices_subset_interior (P : Polygon) : ¬ P.vertices ⊆ P.interior := by
  intro h
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  exact ((P.mem_interior v).mp (h hv)).2 hv

theorem Polygon.not_mutually_nested (P Q : Polygon) (h : P.vertices ⊆ Q.interior) :
    ¬ Q.vertices ⊆ P.interior := by
  intro h'
  have hl := P.interior_card_lt Q.interior Q.interior_filled ((mem_polygons _ _).mpr h)
  have hl' := Q.interior_card_lt P.interior P.interior_filled ((mem_polygons _ _).mpr h')
  omega

 

theorem polygonSystem_outermost (D : Finset Vertex) (f : FaceIndex) (S : Finset Polygon)
    (hS : S ∈ polygonSystems D f) (hne : S.Nonempty) :
    ∃ P ∈ S, ∀ Q ∈ S, Q ≠ P → Q.vertices ⊆ P.interior := by
  obtain ⟨P,hP,hmax⟩ := S.exists_max_image (fun P => P.interior.card) hne
  refine ⟨P,hP,?_⟩
  intro Q hQ hneq
  have hs := (mem_polygonSystems D f S).mp hS
  rcases Q.disjoint_common_face_nested P (hs.2.1 hQ hP hneq) f
    (hs.2.2 Q hQ) (hs.2.2 P hP) with h | h
  · exact h
  · have hl := P.interior_card_lt Q.interior Q.interior_filled ((mem_polygons _ _).mpr h)
    have hm := hmax Q hQ
    omega

theorem polygonSystem_erase_outermost (D : Finset Vertex) (f : FaceIndex) (S : Finset Polygon)
    (hS : S ∈ polygonSystems D f) (P : Polygon)
    (hout : ∀ Q ∈ S, Q ≠ P → Q.vertices ⊆ P.interior) :
    S.erase P ∈ polygonSystems P.interior f := by
  classical
  have hs := (mem_polygonSystems D f S).mp hS
  apply (mem_polygonSystems _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro Q hQ
    exact (mem_polygons _ _).mpr (hout Q (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))
  · intro Q hQ R hR hne
    exact hs.2.1 (Finset.mem_of_mem_erase hQ) (Finset.mem_of_mem_erase hR) hne
  · intro Q hQ
    exact hs.2.2 Q (Finset.mem_of_mem_erase hQ)

theorem not_mem_interior_system (P : Polygon) (f : FaceIndex) (S : Finset Polygon)
    (hS : S ∈ polygonSystems P.interior f) : P ∉ S := by
  intro hP
  exact P.not_vertices_subset_interior ((mem_polygons _ _).mp
    (((mem_polygonSystems _ _ _).mp hS).1 hP))

theorem polygonSystem_insert_outer (D : Finset Vertex) (f : FaceIndex) (P : Polygon)
    (hD : Filled D) (hP : P ∈ polygons D) (hf : f ∈ P.interiorFaces)
    (S : Finset Polygon) (hS : S ∈ polygonSystems P.interior f) :
    insert P S ∈ polygonSystems D f := by
  classical
  have hs := (mem_polygonSystems _ _ _).mp hS
  have hQ (Q : Polygon) (hQ : Q ∈ S) : Q.vertices ⊆ P.interior :=
    (mem_polygons _ _).mp (hs.1 hQ)
  have hdis (Q : Polygon) (hq : Q ∈ S) : Disjoint P.vertices Q.vertices := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvQ
    exact ((P.mem_interior v).mp (hQ Q hq hvQ)).2 hvP
  apply (mem_polygonSystems _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro Q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hP
    · exact (mem_polygons _ _).mpr ((hQ Q hq).trans (hD P hP))
  · intro Q hq R hr hne
    rcases Finset.mem_insert.mp hq with hQP | hQS
    · subst Q
      rcases Finset.mem_insert.mp hr with hRP | hRS
      · exact (hne hRP.symm).elim
      · exact hdis R hRS
    · rcases Finset.mem_insert.mp hr with hRP | hRS
      · subst R
        exact (hdis Q hQS).symm
      · exact hs.2.1 hQS hRS hne
  · intro Q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hf
    · exact hs.2.2 Q hq

 
theorem polygonSystem_insert_unique (f : FaceIndex) (P Q : Polygon) (S T : Finset Polygon)
    (hS : S ∈ polygonSystems P.interior f) (hT : T ∈ polygonSystems Q.interior f)
    (he : insert P S = insert Q T) : P = Q := by
  classical
  by_contra hn
  have hp : P ∈ T := by
    have : P ∈ insert Q T := he ▸ Finset.mem_insert_self P S
    exact (Finset.mem_insert.mp this).resolve_left hn
  have hq : Q ∈ S := by
    have : Q ∈ insert P S := he.symm ▸ Finset.mem_insert_self Q T
    exact (Finset.mem_insert.mp this).resolve_left (Ne.symm hn)
  exact P.not_mutually_nested Q
    ((mem_polygons _ _).mp (((mem_polygonSystems _ _ _).mp hT).1 hp))
    ((mem_polygons _ _).mp (((mem_polygonSystems _ _ _).mp hS).1 hq))

noncomputable def outerSystems (P : Polygon) (f : FaceIndex) : Finset (Finset Polygon) := by
  classical
  exact if f ∈ P.interiorFaces then (polygonSystems P.interior f).image (insert P) else ∅

theorem polygonSystems_split (D : Finset Vertex) (f : FaceIndex) (hD : Filled D) :
    polygonSystems D f = insert ∅ ((polygons D).biUnion (fun P => outerSystems P f)) := by
  classical
  ext S
  constructor
  · intro hS
    by_cases h0 : S = ∅
    · simp [h0]
    · obtain ⟨P,hP,hout⟩ := polygonSystem_outermost D f S hS (Finset.nonempty_iff_ne_empty.mpr h0)
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨P,((mem_polygonSystems D f S).mp hS).1 hP,?_⟩
      rw [outerSystems,ite_eq_left (((mem_polygonSystems D f S).mp hS).2.2 P hP)]
      exact Finset.mem_image.mpr ⟨S.erase P,polygonSystem_erase_outermost D f S hS P hout,
        Finset.insert_erase hP⟩
  · intro hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact empty_mem_polygonSystems D f
    · obtain ⟨P,hP,hS⟩ := Finset.mem_biUnion.mp hS
      by_cases hf : f ∈ P.interiorFaces
      · simp only [outerSystems,ite_eq_left hf,Finset.mem_image] at hS
        obtain ⟨T,hT,rfl⟩ := hS
        exact polygonSystem_insert_outer D f P hD hP hf T hT
      · simp [outerSystems,hf] at hS

theorem outerSystems_disjoint (f : FaceIndex) (P Q : Polygon) (hne : P ≠ Q) :
    Disjoint (outerSystems P f) (outerSystems Q f) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hP hQ
  by_cases hf : f ∈ P.interiorFaces
  · by_cases hf' : f ∈ Q.interiorFaces
    · simp only [outerSystems,ite_eq_left hf,ite_eq_left hf',Finset.mem_image] at hP hQ
      obtain ⟨T,hT,hT'⟩ := hP
      obtain ⟨U,hU,hU'⟩ := hQ
      exact hne (polygonSystem_insert_unique f P Q T U hT hU (hT'.trans hU'.symm))
    · simp [outerSystems,hf'] at hQ
  · simp [outerSystems,hf] at hP

theorem empty_not_mem_outerSystems (P : Polygon) (f : FaceIndex) : ∅ ∉ outerSystems P f := by
  classical
  unfold outerSystems
  split_ifs <;> simp

 
theorem faceNestingMass_recursion (D : Finset Vertex) (f : FaceIndex) (hD : Filled D) :
    faceNestingMass D f = 1 + ∑ P ∈ polygons D, if f ∈ P.interiorFaces then
      2 * criticalActivity ^ P.length * faceNestingMass P.interior f else 0 := by
  classical
  unfold faceNestingMass
  rw [polygonSystems_split D f hD,Finset.sum_insert]
  · simp only [Finset.prod_empty]
    congr 1
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro P hP
      rw [outerSystems]
      split_ifs with hf
      · rw [Finset.sum_image]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.prod_insert (not_mem_interior_system P f S hS)
        · intro S hS T hT he
          have hs := not_mem_interior_system P f S hS
          have ht := not_mem_interior_system P f T hT
          have h := congrArg (fun U : Finset Polygon => U.erase P) he
          simpa [hs,ht] using h
      · simp
    · intro P hP Q hQ hne
      exact outerSystems_disjoint f P Q hne
  · intro hn
    obtain ⟨P,hP,h0⟩ := Finset.mem_biUnion.mp hn
    exact empty_not_mem_outerSystems P f h0

end PolynomialVacuumBridge.Corridor

end OAI

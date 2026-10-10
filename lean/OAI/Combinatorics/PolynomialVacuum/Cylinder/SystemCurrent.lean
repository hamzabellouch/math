import OAI.Combinatorics.PolynomialVacuum.Cylinder.PolygonNetwork

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

noncomputable def signedPolygonCurrent (P : Polygon M) (o : Bool) : Edge M →₀ ℤ :=
  if o then polygonCurrent P else -polygonCurrent P

@[simp] theorem signedPolygonCurrent_support (P : Polygon M) (o : Bool) :
    (signedPolygonCurrent P o).support=P.val := by
  cases o <;> simp [signedPolygonCurrent,polygonCurrent_support]

theorem signedPolygonCurrent_localIce (P : Polygon M) (o : Bool) :
    ∀ v,LocalIce (signedPolygonCurrent P o) v := by
  cases o <;> simp only [signedPolygonCurrent,Bool.false_eq_true,ite_false,ite_true]
  · intro v; exact (polygonCurrent_localIce P v).neg
  · exact polygonCurrent_localIce P

noncomputable def systemCurrent (S : Finset (Polygon M)) (o : Polygon M → Bool) : Edge M →₀ ℤ :=
  ∑ P∈S,signedPolygonCurrent P (o P)

theorem systemCurrent_at (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (P : Polygon M) (hP : P∈S) (v : Vertex M) (hv : v∈P.vertices) (k : Fin 3) :
    orientedFlow (systemCurrent S o) (v,k)=orientedFlow (signedPolygonCurrent P (o P)) (v,k) := by
  simp only [systemCurrent,map_sum,Finsupp.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_eq_single P
  · intro Q hQ hQP
    apply flow_zero_outside_vertices _ Q (by rw [signedPolygonCurrent_support])
    exact fun hQv => Finset.disjoint_left.mp (hS hP hQ hQP.symm) hv hQv
  · simp [hP]

theorem systemCurrent_outside (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (v : Vertex M) (hv : v∉S.biUnion Polygon.vertices) (k : Fin 3) :
    orientedFlow (systemCurrent S o) (v,k)=0 := by
  simp only [systemCurrent,map_sum,Finsupp.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro P hP
  exact flow_zero_outside_vertices _ P (by rw [signedPolygonCurrent_support]) v
    (fun h => hv (Finset.mem_biUnion.mpr ⟨P,hP,h⟩)) k

theorem systemCurrent_localIce (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices)) :
    ∀ v,LocalIce (systemCurrent S o) v := by
  intro v
  by_cases hv : v∈S.biUnion Polygon.vertices
  · obtain ⟨P,hP,hv⟩:=Finset.mem_biUnion.mp hv
    have h:=signedPolygonCurrent_localIce P (o P) v
    unfold LocalIce at h ⊢
    simpa only [systemCurrent_at S o hS P hP v hv] using h
  · exact Or.inl (systemCurrent_outside S o v hv)

 

theorem ice_current_orientation_decomposition (q : Edge M →₀ ℤ) (hq : ∀ v,LocalIce q v) :
    ∃ o : Polygon M → Bool, q=systemCurrent (IceNetwork.network q hq).polygons o := by
  let C:=IceNetwork.network q hq
  have hh : ∀ P∈C.polygons,∃ o : Bool,C.componentFlow P=signedPolygonCurrent P o := by
    intro P hP
    rcases polygon_current_two_orientations P (C.componentFlow P)
      (C.component_flow_localIce P hP) (C.componentFlow_support P hP) with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  let o : Polygon M → Bool:=fun P => if hP : P∈C.polygons then (hh P hP).choose else false
  refine ⟨o,?_⟩
  calc
    q=C.flow := (IceNetwork.recover_flow q hq).symm
    _=systemCurrent C.polygons o := by
      rw [C.flow_sum_components]
      apply Finset.sum_congr rfl
      intro P hP
      exact (show C.componentFlow P=signedPolygonCurrent P (o P) from by
        dsimp only [o]; rw [dite_eq_left hP]; exact (hh P hP).choose_spec)

end PolynomialVacuumCylinder

end OAI

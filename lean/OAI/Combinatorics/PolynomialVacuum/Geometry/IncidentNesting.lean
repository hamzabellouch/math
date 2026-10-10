import OAI.Combinatorics.PolynomialVacuum.Bridge.NestingSystems

namespace OAI

namespace PolynomialVacuumBridge.Corridor

namespace Polygon

theorem incident_mem_of_interior (P : Polygon) (v : Vertex) (hv : v ∈ P.interior) (k : Fin 3) :
    leftFace (v,k) ∈ P.interiorFaces := by
  have h := (P.interior_iff_level v).mp hv
  change leftFace (v,k) ∈ P.potential.support
  rw [Finsupp.mem_support_iff,(P.off_boundary_faces v h.1 k).1]
  exact h.2

theorem incident_mem_implies_closed (P : Polygon) (v : Vertex) (k : Fin 3)
    (hf : leftFace (v,k) ∈ P.interiorFaces) : v ∈ P.vertices ∨ v ∈ P.interior := by
  by_cases hv : v ∈ P.vertices
  · exact Or.inl hv
  · right
    rw [P.mem_interior]
    exact ⟨(mem_cellVertices _ _).mpr ⟨k,hf⟩,hv⟩

theorem incident_not_mem_of_exterior (P : Polygon) (v : Vertex)
    (hb : v ∉ P.vertices) (hi : v ∉ P.interior) (k : Fin 3) :
    leftFace (v,k) ∉ P.interiorFaces := by
  intro hf
  rcases P.incident_mem_implies_closed v k hf with h | h
  · exact hb h
  · exact hi h

end Polygon

 

theorem polygonSystems_exterior_incident (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∉ D) (k : Fin 3) :
    polygonSystems D (leftFace (v,k)) = {∅} := by
  classical
  ext S
  simp only [Finset.mem_singleton]
  constructor
  · intro hS
    have hs := (mem_polygonSystems _ _ _).mp hS
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    have hp := hs.1 hP
    rcases P.incident_mem_implies_closed v k (hs.2.2 P hP) with h | h
    · exact hv ((mem_polygons _ _).mp hp h)
    · exact hv (hD P hp h)
  · rintro rfl
    exact empty_mem_polygonSystems _ _

theorem faceNestingMass_exterior_incident (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∉ D) (k : Fin 3) :
    faceNestingMass D (leftFace (v,k)) = 1 := by
  rw [faceNestingMass,polygonSystems_exterior_incident D v hD hv k]
  simp

noncomputable def incidentNestingMass (D : Finset Vertex) (v : Vertex) : ℝ :=
  ∑ k : Fin 3, faceNestingMass D (leftFace (v,k))

theorem incident_layer_sum (P : Polygon) (v : Vertex) :
    (∑ k : Fin 3, if leftFace (v,k) ∈ P.interiorFaces then
      2 * criticalActivity ^ P.length * faceNestingMass P.interior (leftFace (v,k)) else 0) =
    (if v ∈ P.vertices then 2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length else 0) +
    (if v ∈ P.interior then 2 * criticalActivity ^ P.length * incidentNestingMass P.interior v else 0) := by
  classical
  by_cases hb : v ∈ P.vertices
  · have hi : v ∉ P.interior := fun h => ((P.mem_interior v).mp h).2 hb
    rw [ite_eq_left hb,ite_eq_right hi,add_zero]
    simp_rw [faceNestingMass_exterior_incident P.interior v P.interior_filled hi,mul_one]
    have hc : (faceCount P.interiorFaces v : ℝ) =
        ∑ k : Fin 3, if leftFace (v,k) ∈ P.interiorFaces then (1 : ℝ) else 0 := by
      simp only [faceCount,Int.cast_sum,Int.cast_ite,Int.cast_one,Int.cast_zero]
    rw [hc,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> ring
  · rw [ite_eq_right hb,zero_add]
    by_cases hi : v ∈ P.interior
    · rw [ite_eq_left hi]
      simp only [P.incident_mem_of_interior v hi,ite_true,incidentNestingMass,Finset.mul_sum]
    · rw [ite_eq_right hi]
      simp only [P.incident_not_mem_of_exterior v hb hi,ite_false,Finset.sum_const_zero]

 

theorem incidentNestingMass_recursion (D : Finset Vertex) (v : Vertex) (hD : Filled D) :
    incidentNestingMass D v = 3 +
      (∑ P ∈ polygons D, if v ∈ P.vertices then
        2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length else 0) +
      (∑ P ∈ polygons D, if v ∈ P.interior then
        2 * criticalActivity ^ P.length * incidentNestingMass P.interior v else 0) := by
  classical
  unfold incidentNestingMass at ⊢
  simp_rw [faceNestingMass_recursion D _ hD]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  simp_rw [incident_layer_sum]
  rw [Finset.sum_add_distrib]
  norm_num only [incidentNestingMass,add_assoc,Nat.cast_ofNat]

end PolynomialVacuumBridge.Corridor

end OAI

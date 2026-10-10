import Mathlib
import OAI.Combinatorics.HoneycombCorridor.FaceBoundary

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem faceBoundaryTurn_false (S : Finset FaceIndex) (g : Germ) :
    faceBoundaryTurn S g = false ↔ leftFace (g.1,g.2+1) ∈ S := by
  classical
  simp [faceBoundaryTurn]

theorem star_boundary_outside (D : Finset Vertex) (g : FaceBoundary (starFaces D)) :
    g.val.1 ∉ D := by
  intro hv
  exact g.property.1 (incident_mem_starFaces hv g.val.2)

theorem outside_boundary_germ (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    OnFaceBoundary (starFaces D) (v,k+1) ∧
      faceBoundaryTurn (starFaces D) (v,k+1) = false := by
  have hR : rightFace (v,k) ∈ starFaces D := incident_mem_starFaces hn k
  have hL : leftFace (v,k) ∈ starFaces D := by
    have h := incident_mem_starFaces hn (k+2)
    simpa only [← rightFace_prev,rightFace,reverseGerm,neighbor_neighbor] using h
  have hO := outside_opposite_face D hD v k hv hn
  constructor
  · refine ⟨hO,?_⟩
    rw [rightFace_prev]
    convert hL using 1
    congr 2
    fin_cases k <;> decide
  · rw [faceBoundaryTurn_false]
    simpa only [rightFace_prev,add_assoc,Fin.reduceAdd] using hR

theorem star_boundary_no_double_negative (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (hg : faceBoundaryTurn (starFaces D) g.val = false) :
    faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val = true := by
  classical
  by_contra hn
  have hn' : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val =
      false := by
    cases he : (faceBoundaryTurn (starFaces D)
      (faceBoundaryNext (starFaces D) g).val) <;> simp_all
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp g.property.2
  have hs_mem := (faceBoundaryTurn_false _ _).mp hn'
  have hs_mem' : leftFace (neighbor g.val.1 (g.val.2+1),g.val.2+2) ∈ starFaces D := by
    simpa [faceBoundaryNext,hg,advance,outgoingSlot,add_assoc] using hs_mem
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hs_mem'
  rcases box_two_faces lo hi g.val.1 r s g.val.2 hr hs ((hbox _).mp hr')
    ((hbox _).mp hs') with h | h
  · exact star_boundary_outside D g ((hbox _).mpr h)
  · apply star_boundary_outside D (faceBoundaryNext (starFaces D) g)
    simpa only [faceBoundaryNext,advance,hg,outgoingSlot,Bool.false_eq_true,ite_false]
      using (hbox _).mpr h

noncomputable def boundaryCharge (S : Finset FaceIndex) (g : FaceBoundary S) : ℤ :=
  if faceBoundaryTurn S g.val then 0 else 1

theorem star_boundary_turn_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) :
    boundaryCharge (starFaces D) (faceBoundaryNext (starFaces D) g) -
      boundaryCharge (starFaces D) g ≤ turnUnit (faceBoundaryTurn (starFaces D) g.val) := by
  cases hg : faceBoundaryTurn (starFaces D) g.val
  · have hn := star_boundary_no_double_negative D hD g hg
    simp [boundaryCharge,hg,hn,turnUnit]
  · cases hn : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val <;>
      simp [boundaryCharge,hg,hn,turnUnit]

theorem star_boundary_word_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    boundaryCharge (starFaces D) ((faceBoundaryNext (starFaces D))^[n] g) -
      boundaryCharge (starFaces D) g ≤ turnUnits (faceBoundaryWord (starFaces D) g n) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,turnUnits]
  | succ n ih =>
    have h₁ := star_boundary_turn_charge D hD g
    have h₂ := ih (faceBoundaryNext (starFaces D) g)
    simp only [faceBoundaryWord,turnUnits,List.map_cons,List.sum_cons,
      Function.iterate_succ_apply] at *
    omega

theorem star_boundary_cycle_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val) :
    turnUnits (faceBoundaryWord (starFaces D) g n) = 6 := by
  have hne : faceBoundaryWord (starFaces D) g n ≠ [] := by
    intro he
    have hl := faceBoundaryWord_length (starFaces D) g n
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have h := star_boundary_word_charge D hD g n
  have he : ((faceBoundaryNext (starFaces D))^[n] g) = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  rw [he,sub_self] at h
  rcases simple_polygon_turning g.val _ hne hN hc with h' | h' <;> omega

theorem box_face_row_interval_0 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_1 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_2 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_3 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_4 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_5 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (r s : Vertex)
    (hr : r ∈ faceVertices (i₁,j)) (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact box_face_row_interval_0 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_1 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_2 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_3 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_4 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_5 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'

theorem star_face_row_interval (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (i₁ i i₂ j : ℤ) (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂)
    (hf₁ : (i₁,j) ∈ starFaces D) (hf₂ : (i₂,j) ∈ starFaces D) :
    (i,j) ∈ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf₁
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hf₂
  obtain ⟨v,hv,hv'⟩ := box_face_row_interval lo hi i₁ i i₂ j h₁ h₂ r s hr hs
    ((hbox _).mp hr') ((hbox _).mp hs')
  exact (mem_starFaces D _).mpr ⟨v,hv,(hbox _).mpr hv'⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

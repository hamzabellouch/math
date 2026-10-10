import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Currents

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def rationalFlowComponent (q : EdgeIndex →₀ ℚ) (k : Fin 3) : FaceIndex →₀ ℚ :=
  Finsupp.comapDomain (fun a => (a,k)) q (by intro a _ b _ h; exact (Prod.mk.inj h).1)

theorem conserved_finite_potential (q : EdgeIndex →₀ ℚ) (hq : ConservedCurrent q) :
    ∃ r : FaceIndex →₀ ℚ, faceGradient r = q := by
  let q' : QFlow.FiniteHoneycombFlow := {
    q0 := rationalFlowComponent q 0
    q1 := rationalFlowComponent q 1
    q2 := rationalFlowComponent q 2
    up_conservation := by
      intro i j
      change q ((i,j),0) + q ((i,j),1) + q ((i,j),2) = 0
      simpa [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ,add_assoc] using hq (.up i j)
    down_conservation := by
      intro i j
      have h := hq (.down i j)
      simp [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ] at h
      change q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2) = 0
      linarith }
  obtain ⟨r,hr⟩ := QFlow.finite_flow_is_face_boundary q'
  refine ⟨r,?_⟩
  funext e
  rcases e with ⟨⟨i,j⟩,k⟩
  have h := hr i j
  change q ((i,j),0) = _ ∧ q ((i,j),1) = _ ∧ q ((i,j),2) = _ at h
  fin_cases k <;>
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;>
    tauto

theorem potential_supported_on_cycle_cells (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0)
    (r : FaceIndex →₀ ℚ)
    (hr : ∀ e, e ∉ cellEdges p.support → faceGradient r e = 0) :
    r.support ⊆ p.support := by
  classical
  let pQ : FaceIndex →₀ ℚ := p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)
  let rOut : FaceIndex →₀ ℚ := r.filter (fun a => p a = 0)
  have hpQ (e : EdgeIndex) : faceGradient pQ e = (wordFlow g w e : ℚ) := by
    have h := hp (canonicalDart e)
    rcases e with ⟨⟨i,j⟩,k⟩
    simp only [canonicalDart,upEnd,orientedFlow_up] at h
    simp only [faceGradient,pQ,Finsupp.mapRange_apply]
    exact_mod_cast h.symm
  have hOut : ∀ e, wordFlow g w e = 0 → faceGradient rOut e = 0 := by
    intro e he
    have hpE := hp (canonicalDart e)
    have hz : p (leftFace (canonicalDart e)) = p (rightFace (canonicalDart e)) := by
      rcases e with ⟨⟨i,j⟩,k⟩
      simp only [canonicalDart,upEnd,orientedFlow_up,he] at hpE
      simp only [canonicalDart,upEnd]
      omega
    by_cases hl : p (leftFace (canonicalDart e)) = 0
    · have hrz : p (rightFace (canonicalDart e)) = 0 := hz ▸ hl
      have hout : e ∉ cellEdges p.support := by
        simp [mem_cellEdges,Finsupp.mem_support_iff,hl,hrz]
      simpa [faceGradient,rOut,Finsupp.filter_apply,hl,hrz] using hr e hout
    · have hrz : p (rightFace (canonicalDart e)) ≠ 0 := hz ▸ hl
      simp [faceGradient,rOut,hl,hrz]
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc
    (faceGradient rOut) (gradient_conserved rOut) hOut
  have hEq : rOut = c • pQ := by
    apply finite_gradient_injective
    funext e
    rw [hc' e,← hpQ e]
    simp only [faceGradient,Finsupp.smul_apply,smul_eq_mul]
    ring
  obtain ⟨a,ha⟩ := Finsupp.support_nonempty_iff.mpr hpne
  have hpa : p a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hpQa : pQ a ≠ 0 := by
    simpa only [pQ,Finsupp.mapRange_apply,ne_eq,Int.cast_eq_zero] using hpa
  have hval := congrArg (fun f : FaceIndex →₀ ℚ => f a) hEq
  simp only [rOut,Finsupp.filter_apply,ite_eq_right hpa,Finsupp.smul_apply,smul_eq_mul] at hval
  have hcz : c = 0 := (mul_eq_zero.mp hval.symm).resolve_right hpQa
  have hR : rOut = 0 := by simpa [hcz] using hEq
  intro a ha
  by_contra hnot
  have hpz : p a = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hnot
  have hz := congrArg (fun f : FaceIndex →₀ ℚ => f a) hR
  simp only [rOut,Finsupp.filter_apply,ite_eq_left hpz,Finsupp.zero_apply] at hz
  exact (Finsupp.mem_support_iff.mp ha) hz



theorem edge_mem_around (S : Finset FaceIndex) (g : Germ) :
    edgeOf g ∈ cellEdges S ↔ leftFace g ∈ S ∨ rightFace g ∈ S := by
  rw [mem_cellEdges]
  rcases canonicalDart_edgeOf g with h | h
  · rw [h]
  · rw [h,rightFace_reverse]
    change rightFace g ∈ S ∨ leftFace g ∈ S ↔ _
    exact or_comm

theorem incident_faces_equal (p : FaceIndex →₀ ℤ) (v : Vertex)
    (hp : ∀ k : Fin 3, p (leftFace (v,k)) = p (rightFace (v,k)))
    (k l : Fin 3) : p (leftFace (v,k)) = p (leftFace (v,l)) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  cases v <;> fin_cases k <;> fin_cases l <;>
    simp [leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem nonboundary_vertex_all_edges (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (v : Vertex) (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w)
    (k : Fin 3) : edgeOf (v,k) ∈ cellEdges p.support := by
  have hzero (l : Fin 3) : orientedFlow (wordFlow g w) (v,l) = 0 := by
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v l hnot
  have he (l : Fin 3) : p (leftFace (v,l)) = p (rightFace (v,l)) := by
    have hh := hp (v,l)
    rw [hzero l] at hh
    omega
  obtain ⟨l,hl⟩ := (mem_cellVertices p.support v).mp hv
  rw [edge_mem_around]
  apply Or.inl
  rw [Finsupp.mem_support_iff] at hl ⊢
  rwa [incident_faces_equal p v he k l]

theorem finite_vertex_flat_zero (f : Vertex →₀ ℚ)
    (hf : ∀ v k, f (neighbor v k) = f v) : f = 0 := by
  classical
  let row : Vertex → ℤ := fun v => match v with | .up _ j => j | .down _ j => j
  let M : ℕ := f.support.sup fun v => (row v).natAbs
  have hu (i j : ℤ) : f (.up i j) = 0 := by
    have hh (k : ℤ) : f (.up i (k+1)) = f (.up i k) := by
      have h0 := hf (.down i k) 0
      have h1 := hf (.down i k) 1
      simp only [neighbor,↓reduceIte,Fin.isValue] at h0 h1
      exact h0.trans h1.symm
    let k : ℤ := (M : ℤ) + 1
    have he := QFlow.int_function_constant (f := fun j => f (.up i j)) hh j k
    rw [he]
    by_contra hk
    have hb : (row (.up i k)).natAbs ≤ M :=
      Finset.le_sup (f := fun v : Vertex => (row v).natAbs)
        (Finsupp.mem_support_iff.mpr hk)
    dsimp [row,k] at hb
    omega
  ext v
  cases v with
  | up i j => exact hu i j
  | down i j =>
      have h := hf (.down i j) 1
      simpa [neighbor,hu] using h.symm

theorem flat_along_dart (S : Finset FaceIndex) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges S, f (upEnd e) = f (downEnd e))
    (g : Germ) (h : edgeOf g ∈ cellEdges S) : f (neighbor g.1 g.2) = f g.1 := by
  have he := hf (edgeOf g) h
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [edgeOf,upEnd,downEnd,neighbor] at he ⊢ <;> first | exact he.symm | exact he

theorem cell_flat_zero_boundary (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (f : Vertex →₀ ℚ) (hS : f.support ⊆ cellVertices p.support)
    (hflat : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (hbd : ∀ v ∈ traced g w, f v = 0) : f = 0 := by
  apply finite_vertex_flat_zero
  intro v k
  by_cases he : edgeOf (v,k) ∈ cellEdges p.support
  · exact flat_along_dart _ f hflat (v,k) he
  · have hz (d : Germ) (h : edgeOf d ∉ cellEdges p.support) : f d.1 = 0 := by
      by_cases hV : d.1 ∈ cellVertices p.support
      · apply hbd
        by_contra hnot
        exact h (nonboundary_vertex_all_edges g w hc p hp d.1 hV hnot d.2)
      · by_contra hne
        exact hV (hS (Finsupp.mem_support_iff.mpr hne))
    rw [hz (v,k) he]
    exact hz (reverseGerm (v,k)) (by simpa using he)

end PolynomialVacuumBridge.Corridor

end

end OAI

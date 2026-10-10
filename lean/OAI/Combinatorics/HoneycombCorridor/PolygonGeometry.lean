import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Polygons

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def toRatFinsupp {α : Type*} (p : α →₀ ℤ) : α →₀ ℚ :=
  p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)

@[simp] theorem toRatFinsupp_apply {α : Type*} (p : α →₀ ℤ) (a : α) :
    toRatFinsupp p a = (p a : ℚ) := rfl

@[simp] theorem toRatFinsupp_support {α : Type*} (p : α →₀ ℤ) :
    (toRatFinsupp p).support = p.support := by
  ext a
  simp [Finsupp.mem_support_iff]

theorem RepresentsFlow.rational {p : FaceIndex →₀ ℤ} {q : EdgeIndex →₀ ℤ}
    (hp : RepresentsFlow p q) : faceGradient (toRatFinsupp p) = toRatFinsupp q := by
  funext e
  have h := hp (canonicalDart e)
  rcases e with ⟨⟨i,j⟩,k⟩
  simp only [canonicalDart,upEnd,orientedFlow_up] at h
  simp only [faceGradient,toRatFinsupp_apply]
  exact_mod_cast h.symm

theorem cycle_potential_support_subset (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p r : FaceIndex →₀ ℤ) (s : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (hr : RepresentsFlow r s)
    (hs : s.support ⊆ (wordFlow g w).support) : r.support ⊆ p.support := by
  have hq : ConservedCurrent (toRatFinsupp s) := by
    rw [← hr.rational]
    exact gradient_conserved _
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc (toRatFinsupp s) hq (by
    intro e he
    have haz : s e = 0 := by
      by_contra hz
      have hm := hs (Finsupp.mem_support_iff.mpr hz)
      exact (Finsupp.mem_support_iff.mp hm) he
    simp [haz])
  have he : toRatFinsupp r = c • toRatFinsupp p := by
    apply finite_gradient_injective
    funext e
    have hz := congrFun hp.rational e
    have hy := congrFun hr.rational e
    change faceGradient (toRatFinsupp r) e = _
    rw [hy,hc' e]
    simp only [faceGradient,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]
    rw [← mul_sub]
    exact congrArg (c * ·) hz.symm
  intro a ha
  rw [Finsupp.mem_support_iff] at ha ⊢
  intro hpz
  have h := congrArg (fun t : FaceIndex →₀ ℚ => t a) he
  simp [hpz] at h
  exact ha h

theorem cycle_potential_support_eq (g h : Germ) (w u : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hu : (traced h u).Nodup) (hd : terminalGerm h u = h)
    (p r : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hr : RepresentsFlow r (wordFlow h u))
    (hs : (wordFlow g w).support = (wordFlow h u).support) :
    p.support = r.support := by
  apply Finset.Subset.antisymm
  · exact cycle_potential_support_subset h u hu hd r p (wordFlow g w) hr hp hs.le
  · exact cycle_potential_support_subset g w hw hc p r (wordFlow h u) hp hr hs.ge

def edgeVertices (E : Finset EdgeIndex) : Finset Vertex := E.biUnion fun e => {upEnd e,downEnd e}

@[simp] theorem mem_edgeVertices (E : Finset EdgeIndex) (v : Vertex) :
    v ∈ edgeVertices E ↔ ∃ k : Fin 3, edgeOf (v,k) ∈ E := by
  classical
  constructor
  · intro h
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine ⟨e.2,?_⟩
      change edgeOf (canonicalDart e) ∈ E
      simpa using he
    · exact ⟨e.2,by simpa using he⟩
  · rintro ⟨k,hk⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨edgeOf (v,k),hk,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact (edgeOf_eq_iff v (edgeOf (v,k))).mp (by simp)

theorem wordContour_has_edge (q : EdgeIndex →₀ ℤ) (g : Germ) (w : List Bool)
    (hw : WordContour q g w) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ k : Fin 3, q (edgeOf (v,k)) ≠ 0 := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨outgoingSlot g b, fun hz => contour_outgoing_nonzero q g b hw.1
          ((orientedFlow_zero_iff q _).mpr hz)⟩
      · exact ih _ hw.2 hv

theorem wordFlow_edgeVertices (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    edgeVertices (wordFlow g w).support = (traced g w).toFinset := by
  classical
  ext v
  simp only [mem_edgeVertices,Finsupp.mem_support_iff,List.mem_toFinset]
  constructor
  · rintro ⟨k,hk⟩
    by_contra hn
    have h := turnVisit_eq_zero_of_not_mem g w v k hn
    have hz : orientedFlow (wordFlow g w) (v,k) = 0 := by
      rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
      exact h
    exact hk ((orientedFlow_zero_iff _ _).mp hz)
  · exact wordContour_has_edge _ g w (simple_closed_word_contour g w hw hc) v

namespace Polygon

theorem vertices_traversal (P : Polygon) : P.vertices = (traced P.germ P.turns).toFinset := by
  change edgeVertices P.val = _
  rw [← P.traversal.2.2.2]
  exact wordFlow_edgeVertices _ _ P.traversal.2.1 P.traversal.2.2.1

theorem interiorFaces_of_traversal (P : Polygon) (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hE : (wordFlow g w).support = P.val) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) : P.interiorFaces = p.support := by
  apply cycle_potential_support_eq P.germ g P.turns w P.traversal.2.1
    P.traversal.2.2.1 hw hc P.potential p P.potential_spec.1 hp
  exact P.traversal.2.2.2.trans hE.symm

@[simp] theorem mem_interior (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∈ cellVertices P.interiorFaces ∧ v ∉ P.vertices := by
  simp [interior]

end Polygon


@[simp] theorem mem_inducedEdges (D : Finset Vertex) (e : EdgeIndex) :
    e ∈ inducedEdges D ↔ upEnd e ∈ D ∧ downEnd e ∈ D := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨canonicalDart e,?_,edgeOf_canonical e⟩,h⟩
    exact Finset.mem_product.mpr ⟨h.1,Finset.mem_univ _⟩

@[simp] theorem mem_polygons (D : Finset Vertex) (P : Polygon) :
    P ∈ polygons D ↔ P.vertices ⊆ D := by
  classical
  have hm : P ∈ polygons D ↔ P.val ⊆ inducedEdges D := by
    simp [polygons]
  rw [hm]
  constructor
  · intro h v hv
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
    have he' := (mem_inducedEdges D e).mp (h he)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact he'.1
    · exact he'.2
  · intro h e he
    apply (mem_inducedEdges D e).mpr
    constructor
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)

noncomputable def vertexLevel (p : FaceIndex →₀ ℤ) (v : Vertex) : ℤ :=
  p (leftFace (v,0))

namespace Polygon

theorem represents (P : Polygon) : RepresentsFlow P.potential (wordFlow P.germ P.turns) :=
  P.potential_spec.1

theorem off_boundary_zero (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    orientedFlow (wordFlow P.germ P.turns) (v,k) = 0 := by
  apply (orientedFlow_zero_iff _ _).mpr
  by_contra hn
  apply hv
  change v ∈ edgeVertices P.val
  apply (mem_edgeVertices _ _).mpr
  exact ⟨k,by rw [← P.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn⟩

theorem off_boundary_faces (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    P.potential (leftFace (v,k)) = vertexLevel P.potential v ∧
    P.potential (rightFace (v,k)) = vertexLevel P.potential v := by
  have he (l : Fin 3) : P.potential (leftFace (v,l)) = P.potential (rightFace (v,l)) := by
    have h := P.represents (v,l)
    rw [P.off_boundary_zero v hv l] at h
    omega
  have hl := incident_faces_equal P.potential v he k 0
  exact ⟨hl,(he k).symm.trans hl⟩

theorem interior_iff_level (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∉ P.vertices ∧ vertexLevel P.potential v ≠ 0 := by
  rw [P.mem_interior,mem_cellVertices]
  constructor
  · rintro ⟨⟨k,hk⟩,hv⟩
    refine ⟨hv,?_⟩
    change leftFace (v,k) ∈ P.potential.support at hk
    rw [Finsupp.mem_support_iff] at hk
    rwa [(P.off_boundary_faces v hv k).1] at hk
  · rintro ⟨hv,hl⟩
    exact ⟨⟨0,Finsupp.mem_support_iff.mpr hl⟩,hv⟩

theorem step_level (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∉ P.vertices) (hu : neighbor v k ∉ P.vertices) :
    vertexLevel P.potential (neighbor v k) = vertexLevel P.potential v := by
  rw [← (P.off_boundary_faces (neighbor v k) hu k).1]
  change P.potential (leftFace (reverseGerm (v,k))) = _
  exact (P.off_boundary_faces v hv k).2

theorem interior_exit_on_boundary (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∈ P.interior) (hu : neighbor v k ∉ P.interior) :
    neighbor v k ∈ P.vertices := by
  by_contra hn
  apply hu
  rw [P.interior_iff_level]
  have h := (P.interior_iff_level v).mp hv
  exact ⟨hn,by rw [P.step_level v k h.1 hn]; exact h.2⟩

theorem trace_level (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices)
    (ht : (terminalGerm g w).1 ∉ P.vertices) :
    vertexLevel P.potential (terminalGerm g w).1 = vertexLevel P.potential g.1 := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      have hg : g.1 ∉ P.vertices := hdis _ (by simp [traced])
      have ha : (advance g b).1 ∉ P.vertices := by
        cases w with
        | nil => exact ht
        | cons c w => exact hdis _ (by simp [traced])
      have htail : ∀ v ∈ traced (advance g b) w, v ∉ P.vertices := by
        intro v hv
        exact hdis v (List.mem_cons_of_mem _ hv)
      exact (ih (advance g b) htail ht).trans (P.step_level g.1 (outgoingSlot g b) hg ha)

theorem trace_left_potential (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices) :
    P.potential (leftFace (terminalGerm g w)) = P.potential (leftFace g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      have hg : g.1 ∉ P.vertices := hdis _ (by simp [traced])
      have htail : ∀ v ∈ traced (advance g b) w, v ∉ P.vertices := by
        intro v hv
        exact hdis v (List.mem_cons_of_mem _ hv)
      change P.potential (leftFace (terminalGerm (advance g b) w)) = _
      rw [ih (advance g b) htail]
      change P.potential (rightFace (g.1,outgoingSlot g b)) = _
      rw [(P.off_boundary_faces g.1 hg (outgoingSlot g b)).2]
      exact (P.off_boundary_faces g.1 hg g.2).1.symm

theorem outside_level_zero (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (v : Vertex) (hv : v ∉ D) :
    vertexLevel P.potential v = 0 := by
  by_contra hn
  have hb : v ∉ P.vertices := fun h => hv ((mem_polygons D P).mp hP h)
  have hi := (P.interior_iff_level v).mpr ⟨hb,hn⟩
  exact hv (hD P hP hi)

theorem outside_port_potential (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (g : Germ) (hg : (reverseGerm g).1 ∉ D) :
    P.potential (leftFace g) = 0 := by
  have hb : (reverseGerm g).1 ∉ P.vertices :=
    fun h => hg ((mem_polygons D P).mp hP h)
  have he := (P.off_boundary_faces (reverseGerm g).1 hb g.2).2
  have hr : rightFace ((reverseGerm g).1,g.2) = leftFace g := by
    change leftFace (reverseGerm (reverseGerm g)) = _
    rw [reverseGerm_reverseGerm]
  rw [hr] at he
  exact he.trans (P.outside_level_zero D hD hP _ hg)

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI

import Mathlib
import OAI.Combinatorics.HoneycombCorridor.PolygonGeometry
import OAI.Combinatorics.HoneycombCorridor.BoundaryCharge
import OAI.Combinatorics.HoneycombCorridor.CollisionPhase

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def faceIndicator (S : Finset FaceIndex) (a : FaceIndex) : ℤ := if a ∈ S then 1 else 0

theorem faceBoundary_local (S : Finset FaceIndex) (g : FaceBoundary S) (k : Fin 3) :
    faceIndicator S (leftFace (g.val.1,k)) - faceIndicator S (rightFace (g.val.1,k)) =
    (if k = outgoingSlot g.val (faceBoundaryTurn S g.val) then 1 else 0) -
      (if k = g.val.2 then 1 else 0) := by
  classical
  rcases g with ⟨⟨v,l⟩,h⟩
  simp only [OnFaceBoundary,rightFace_prev] at h
  by_cases ht : leftFace (v,l+1) ∈ S
  · simp only [faceBoundaryTurn,ht,not_true_eq_false,decide_false]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]
  · simp only [faceBoundaryTurn,ht,not_false_eq_true,decide_true]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]

theorem faceBoundaryWord_local (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (q : EdgeIndex →₀ ℤ)
    (hq : WordContour q g.val (faceBoundaryWord S g n)) :
    ∀ v ∈ traced g.val (faceBoundaryWord S g n), ∀ k : Fin 3,
      orientedFlow q (v,k) = faceIndicator S (leftFace (v,k)) -
        faceIndicator S (rightFace (v,k)) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    intro v hv k
    simp only [faceBoundaryWord,traced,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (hq.1 k).trans (faceBoundary_local S g k).symm
    · exact ih (faceBoundaryNext S g) hq.2 v hv k

theorem faceBoundaryWord_gradient (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (hN : (traced g.val (faceBoundaryWord S g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord S g n) = g.val)
    (e : EdgeIndex) (he : wordFlow g.val (faceBoundaryWord S g n) e ≠ 0) :
    wordFlow g.val (faceBoundaryWord S g n) e =
      faceIndicator S (leftFace (canonicalDart e)) -
        faceIndicator S (rightFace (canonicalDart e)) := by
  have hv : upEnd e ∈ traced g.val (faceBoundaryWord S g n) := by
    have hm : upEnd e ∈ edgeVertices (wordFlow g.val (faceBoundaryWord S g n)).support := by
      apply Finset.mem_biUnion.mpr
      exact ⟨e,Finsupp.mem_support_iff.mpr he,by simp⟩
    rwa [wordFlow_edgeVertices _ _ hN hc,List.mem_toFinset] at hm
  have h := faceBoundaryWord_local S g n _ (simple_closed_word_contour _ _ hN hc)
    _ hv e.2
  rcases e with ⟨⟨i,j⟩,k⟩
  simpa only [upEnd,canonicalDart,orientedFlow_up] using h

theorem finite_indicator_row_containment (p : FaceIndex →₀ ℤ) (S : Finset FaceIndex)
    (hval : ∀ a, p a = 0 ∨ p a = 1)
    (hgrad : ∀ i j : ℤ, p (i,j) ≠ p (i-1,j) →
      p (i,j) - p (i-1,j) = faceIndicator S (i,j) - faceIndicator S (i-1,j))
    (hrow : ∀ i₁ i i₂ j : ℤ, i₁ ≤ i → i ≤ i₂ → (i₁,j) ∈ S → (i₂,j) ∈ S →
      (i,j) ∈ S) : p.support ⊆ S := by
  classical
  rintro ⟨i,j⟩ ha
  let R := (p.support.filter fun a => a.2 = j).image Prod.fst
  have hRmem (x : ℤ) : x ∈ R ↔ p (x,j) ≠ 0 := by
    simp only [R,Finset.mem_image,Finset.mem_filter,Finsupp.mem_support_iff]
    constructor
    · rintro ⟨⟨u,v⟩,⟨hp,hj⟩,hi⟩
      dsimp at hj hi
      subst v; subst u
      exact hp
    · intro hx
      exact ⟨(x,j),⟨hx,rfl⟩,rfl⟩
  have hi : i ∈ R := (hRmem i).mpr (Finsupp.mem_support_iff.mp ha)
  have hne : R.Nonempty := ⟨i,hi⟩
  let a := R.min' hne
  let b := R.max' hne
  have haR : a ∈ R := R.min'_mem hne
  have hbR : b ∈ R := R.max'_mem hne
  have hpa : p (a,j) = 1 := (hval _).resolve_left ((hRmem a).mp haR)
  have hpb : p (b,j) = 1 := (hval _).resolve_left ((hRmem b).mp hbR)
  have hpa' : p (a-1,j) = 0 := by
    by_contra hz
    have hm := R.min'_le (a-1) ((hRmem _).mpr hz)
    change a ≤ a-1 at hm
    omega
  have hpb' : p (b+1,j) = 0 := by
    by_contra hz
    have hm := R.le_max' (b+1) ((hRmem _).mpr hz)
    change b+1 ≤ b at hm
    omega
  have haS : (a,j) ∈ S := by
    have h := hgrad a j (by omega)
    rw [hpa,hpa'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  have hbS : (b,j) ∈ S := by
    have he : b+1-1 = b := by omega
    have h := hgrad (b+1) j (by rw [he,hpb,hpb']; norm_num)
    rw [he,hpb,hpb'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  exact hrow a i b j (R.min'_le _ hi) (R.le_max' _ hi) haS hbS

theorem star_boundary_potential_contained (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p
      (wordFlow g.val (faceBoundaryWord (starFaces D) g n)))
    (hval : ∀ a, p a = 0 ∨ p a = 1) : p.support ⊆ starFaces D := by
  apply finite_indicator_row_containment p (starFaces D) hval
  · intro i j he
    have h : wordFlow g.val (faceBoundaryWord (starFaces D) g n) ((i,j),0) ≠ 0 := by
      rw [hp.horizontal]
      exact sub_ne_zero.mpr he
    have he' := faceBoundaryWord_gradient (starFaces D) g n hN hc ((i,j),0) h
    rw [hp.horizontal] at he'
    simpa [canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] using he'
  · exact star_face_row_interval D hD



theorem contour_unused_advance (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (hl : LocalContour q g false) :
    p (leftFace (advance g true)) = p (leftFace (g.1,unusedSlot g false)) := by
  have h := (hp (g.1,unusedSlot g false)).symm.trans (hl (unusedSlot g false))
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [advance,outgoingSlot,unusedSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem star_boundary_trace_outside (D : Finset Vertex)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    ∀ v ∈ traced g.val (faceBoundaryWord (starFaces D) g n), v ∉ D := by
  intro v hv
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hv
  obtain ⟨i,rfl⟩ := hv
  exact star_boundary_outside D _

theorem star_boundary_endpoint (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (hd : ∀ v ∈ traced e w, v ∈ D)
    (hu : (terminalGerm e w).1 ∉ D)
    (hu' : (reverseGerm (terminalGerm e w)).1 ∈ D) :
    (terminalGerm e w).1 ∈ traced g.val (faceBoundaryWord (starFaces D) g n) := by
  classical
  let W := faceBoundaryWord (starFaces D) g n
  have hne : W ≠ [] := by
    intro hx
    have hl := faceBoundaryWord_length (starFaces D) g n
    change W.length = n at hl
    rw [hx] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g.val W hne hN hc
  have ht := simple_polygon_signed_turn g.val W hne hN hc p ε hp hpne hε hvals
  have ht' := star_boundary_cycle_turn D hD g n hn hN hc
  have heps : ε = 1 := by change turnUnits W = 6 at ht'; rw [ht'] at ht; omega
  subst ε
  have hpS := star_boundary_potential_contained D hD g n hN hc p hp hvals
  let P : Polygon := ⟨(wordFlow g.val W).support,⟨g.val,W,hne,hN,hc,rfl⟩⟩
  have hPv : P.vertices = (traced g.val W).toFinset :=
    wordFlow_edgeVertices g.val W hN hc
  have hPf : P.interiorFaces = p.support :=
    P.interiorFaces_of_traversal g.val W hN hc rfl p hp
  have hdis : ∀ v ∈ traced e w, v ∉ P.vertices := by
    intro v hv hm
    rw [hPv,List.mem_toFinset] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  have hlocal : LocalContour (wordFlow g.val W) g.val false := by
    have hh := simple_closed_word_contour g.val W hN hc
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [W,faceBoundaryWord,hg,WordContour] using hh.1
  have hused := contour_unused_face p 1 (Or.inl rfl) hvals _ hp g.val false hlocal
  have hpone : p (leftFace e) = 1 := by
    rw [he,contour_unused_advance p _ hp g.val hlocal]
    norm_num [turnUnit] at hused
    omega
  have hstart : P.potential (leftFace e) ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    change leftFace e ∈ P.interiorFaces
    rw [hPf,Finsupp.mem_support_iff,hpone]
    norm_num
  have hend : P.potential (leftFace (terminalGerm e w)) ≠ 0 := by
    rw [P.trace_left_potential e w hdis]
    exact hstart
  by_contra hout
  have hnot : (terminalGerm e w).1 ∉ P.vertices := by
    simpa only [hPv,List.mem_toFinset] using hout
  have hmiss := (outside_boundary_germ D hD (terminalGerm e w).1
    (terminalGerm e w).2 hu hu').1.1
  have hzero : P.potential (leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1)) = 0 := by
    by_contra hz
    have hm : leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1) ∈ P.interiorFaces :=
      Finsupp.mem_support_iff.mpr hz
    rw [hPf] at hm
    exact hmiss (hpS hm)
  rw [(P.off_boundary_faces _ hnot _).1] at hzero
  apply hend
  exact (P.off_boundary_faces _ hnot _).1.trans hzero

end PolynomialVacuumBridge.Corridor

end

end OAI

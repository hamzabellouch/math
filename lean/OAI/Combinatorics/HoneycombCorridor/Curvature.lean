import Mathlib
import OAI.Combinatorics.HoneycombCorridor.PotentialSupport

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def turnUnit (b : Bool) : ℤ := if b then 1 else -1

def turnUnits (w : List Bool) : ℤ := (w.map turnUnit).sum

def faceCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if leftFace (v,k) ∈ S then 1 else 0

def edgeCount (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if edgeOf (v,k) ∈ cellEdges S then 1 else 0

def cellCurvature (S : Finset FaceIndex) (v : Vertex) : ℤ :=
  6 - 3 * edgeCount S v + faceCount S v

@[simp] theorem rightFace_prev (v : Vertex) (k : Fin 3) :
    rightFace (v,k) = leftFace (v,k+2) := by
  cases v <;> fin_cases k <;> simp [rightFace,reverseGerm,neighbor,leftFace]

theorem leftFace_injective (v : Vertex) : Function.Injective (fun k : Fin 3 => leftFace (v,k)) := by
  intro k l h
  cases v <;> fin_cases k <;> fin_cases l <;> simp [leftFace] at h ⊢ <;> omega

theorem faceCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    faceCount S v = ∑ a ∈ S, if v ∈ faceVertices a then (1 : ℤ) else 0 := by
  classical
  have hpair (a : FaceIndex) : (∑ k : Fin 3, if leftFace (v,k) = a then (1 : ℤ) else 0) =
      if v ∈ faceVertices a then 1 else 0 := by
    by_cases hv : v ∈ faceVertices a
    · obtain ⟨k,hk⟩ := (mem_faceVertices v a).mp hv
      rw [ite_eq_left hv,Finset.sum_eq_single k]
      · simp [hk]
      · intro l _ hl
        have hn : leftFace (v,l) ≠ a := fun h => hl (leftFace_injective v (h.trans hk.symm))
        simp [hn]
      · simp
    · rw [ite_eq_right hv]
      apply Finset.sum_eq_zero
      intro k _
      have hn : leftFace (v,k) ≠ a := fun h => hv ((mem_faceVertices v a).mpr ⟨k,h⟩)
      simp [hn]
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold faceCount
  apply Finset.sum_congr rfl
  intro k _
  simp

@[simp] theorem edgeOf_slot (g : Germ) : (edgeOf g).2 = g.2 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf]

@[simp] theorem edgeOf_canonical (e : EdgeIndex) : edgeOf (canonicalDart e) = e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rfl

@[simp] theorem edgeOf_downEnd (e : EdgeIndex) : edgeOf (downEnd e,e.2) = e := by
  change edgeOf (reverseGerm (canonicalDart e)) = e
  rw [edgeOf_reverse,edgeOf_canonical]

theorem edgeOf_eq_iff (v : Vertex) (e : EdgeIndex) :
    edgeOf (v,e.2) = e ↔ v = upEnd e ∨ v = downEnd e := by
  constructor
  · intro h
    rcases canonicalDart_edgeOf (v,e.2) with h' | h'
    · rw [h] at h'
      exact Or.inl (congrArg Prod.fst h').symm
    · rw [h] at h'
      have he := congrArg (fun x : Germ => (reverseGerm x).1) h'
      simp only [reverseGerm_reverseGerm] at he
      exact Or.inr he.symm
  · rintro (rfl | rfl)
    · exact edgeOf_canonical e
    · exact edgeOf_downEnd e

theorem upEnd_ne_downEnd (e : EdgeIndex) : upEnd e ≠ downEnd e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  fin_cases k <;> simp [upEnd,downEnd,neighbor]

theorem edgeCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    edgeCount S v = ∑ e ∈ cellEdges S,
      ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ) := by
  classical
  have hpair (e : EdgeIndex) : (∑ k : Fin 3, if edgeOf (v,k) = e then (1 : ℤ) else 0) =
      (if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) := by
    rw [Finset.sum_eq_single e.2]
    · simp only [edgeOf_eq_iff]
      by_cases hu : v = upEnd e
      · simp [hu,upEnd_ne_downEnd]
      · by_cases hd : v = downEnd e
        · simp [hd, Ne.symm (upEnd_ne_downEnd e)]
        · simp [hu,hd]
    · intro k _ hk
      have hn : edgeOf (v,k) ≠ e := fun h => hk (by simpa using congrArg Prod.snd h)
      simp [hn]
    · simp
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold edgeCount
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem faceVertices_card (a : FaceIndex) : (faceVertices a).card = 6 := by
  rcases a with ⟨i,j⟩
  simp [faceVertices]

theorem sum_faceCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, faceCount S v = 6 * (S.card : ℤ) := by
  classical
  simp_rw [faceCount_incidence]
  rw [Finset.sum_comm]
  have ha (a : FaceIndex) (hma : a ∈ S) :
      (∑ v ∈ cellVertices S, if v ∈ faceVertices a then (1 : ℤ) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have hF : (cellVertices S).filter (fun v => v ∈ faceVertices a) = faceVertices a := by
      ext v
      simp only [Finset.mem_filter,and_iff_right_iff_imp]
      intro hv
      exact Finset.mem_biUnion.mpr ⟨a,hma,hv⟩
    rw [hF]
    simp [faceVertices_card]
  simp_rw [Finset.sum_congr rfl ha]
  simp [mul_comm]

theorem sum_edgeCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, edgeCount S v = 2 * ((cellEdges S).card : ℤ) := by
  classical
  simp_rw [edgeCount_incidence]
  rw [Finset.sum_comm]
  have he (e : EdgeIndex) (hme : e ∈ cellEdges S) :
      (∑ v ∈ cellVertices S,
        ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ)) = 2 := by
    have hu : upEnd e ∈ cellVertices S :=
      edge_mem_vertex S (canonicalDart e) (by simpa using hme)
    have hd : downEnd e ∈ cellVertices S :=
      edge_mem_neighbor S (canonicalDart e) (by simpa using hme)
    rw [Finset.sum_add_distrib]
    simp [hu,hd]
  simp_rw [Finset.sum_congr rfl he]
  simp [mul_comm]

theorem sum_cellCurvature (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, cellCurvature S v =
      6 * ((cellVertices S).card - (cellEdges S).card + (S.card : ℤ)) := by
  simp only [cellCurvature,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,sum_faceCount,sum_edgeCount]
  simp
  ring

theorem numeric_contour_curvature (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    6 - 3 * (∑ l : Fin 3, if f l ≠ 0 ∨ f (l+2) ≠ 0 then (1 : ℤ) else 0) +
      (∑ l : Fin 3, if f l ≠ 0 then (1 : ℤ) else 0) = ε * turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1 <;>
    rcases hf2 with hf2 | hf2 <;>
    simp only [Fin.sum_univ_succ] at * <;> simp_all [turnUnit]

theorem contour_cellCurvature (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    cellCurvature p.support g.1 = ε * turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hlocal (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  have he := numeric_contour_curvature f ε hε (fun l => hvals _) g.2 b hlocal
  unfold cellCurvature edgeCount faceCount
  simp_rw [edge_mem_around,Finsupp.mem_support_iff,rightFace_prev]
  exact he

theorem nonboundary_cellCurvature (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (v : Vertex)
    (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w) :
    cellCurvature p.support v = 0 := by
  have hE := nonboundary_vertex_all_edges g w hc p hp v hv hnot
  have hz (l : Fin 3) : orientedFlow (wordFlow g w) (v,l) = 0 := by
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v l hnot
  have he (l : Fin 3) : p (leftFace (v,l)) = p (rightFace (v,l)) := by
    have h := hp (v,l)
    rw [hz l] at h
    omega
  obtain ⟨l,hl⟩ := (mem_cellVertices _ v).mp hv
  have hF (k : Fin 3) : leftFace (v,k) ∈ p.support := by
    rw [Finsupp.mem_support_iff] at hl ⊢
    rwa [incident_faces_equal p v he k l]
  simp [cellCurvature,edgeCount,faceCount,hE,hF]

theorem contour_curvature_sum (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ((traced g w).map (cellCurvature p.support)).sum = ε * turnUnits w := by
  induction w generalizing g with
  | nil => simp [traced,turnUnits]
  | cons b w ih =>
      simp only [traced,List.map_cons,List.sum_cons,turnUnits,List.map_cons,List.sum_cons]
      rw [contour_cellCurvature p ε hε hvals q hp g b hw.1,ih _ hw.2]
      simp only [turnUnits]
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI

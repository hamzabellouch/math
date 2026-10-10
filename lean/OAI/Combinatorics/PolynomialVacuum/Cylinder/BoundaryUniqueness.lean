import OAI.Combinatorics.PolynomialVacuum.Cylinder.BoundaryArc

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ} {D : Finset (Vertex M)}

namespace BoundaryArc
variable (A : BoundaryArc D)

theorem start_mem : A.start.1∈A.vertices := by
  obtain ⟨b,w,hw⟩:=List.exists_cons_of_ne_nil A.nonempty
  simp [vertices,hw,traced]

theorem current_at_start : orientedFlow A.current A.start= -1 := by
  obtain ⟨b,w,hw⟩:=List.exists_cons_of_ne_nil A.nonempty
  have hc:=A.contour
  rw [hw] at hc
  have hh:=hc.1 A.start.2
  simpa only [outgoingSlot_ne,Ne.symm (outgoingSlot_ne A.start b),ite_false,ite_true,zero_sub] using hh

theorem ext_data (B : BoundaryArc D) (hs : A.start=B.start) (hw : A.word=B.word) : A=B := by
  cases A
  cases B
  cases hs
  cases hw
  rfl
end BoundaryArc

private theorem not_active_zero (q : Edge M →₀ ℤ) (v : Vertex M) (hv : v∉activeSites q)
    (k : Fin 3) : orientedFlow q (v,k)=0 := by
  by_contra h
  exact hv ((mem_activeSites q v).mpr ⟨k,h⟩)

private theorem arcs_sum_zero (L : List (BoundaryArc D)) (v : Vertex M) (hv : v∈D) (k : Fin 3)
    (hz : ∀A∈L,v∉A.vertices) : orientedFlow ((L.map BoundaryArc.current).sum) (v,k)=0 := by
  induction L with
  | nil => simp
  | cons A L ih =>
    simp only [List.map_cons,List.sum_cons,map_add,Finsupp.add_apply]
    rw [A.current_zero v hv (hz A (by simp)) k,ih (fun B hB => hz B (by simp [hB]))]
    rfl

private theorem arcs_sum_on_member (L : List (BoundaryArc D))
    (hp : L.Pairwise (fun A B => Disjoint A.vertices B.vertices))
    (A : BoundaryArc D) (hA : A∈L) (v : Vertex M) (hv : v∈A.vertices) (k : Fin 3) :
    orientedFlow ((L.map BoundaryArc.current).sum) (v,k)=orientedFlow A.current (v,k) := by
  induction L with
  | nil => simp at hA
  | cons B L ih =>
    obtain ⟨hb,ht⟩:=List.pairwise_cons.mp hp
    simp only [List.map_cons,List.sum_cons,map_add,Finsupp.add_apply]
    rcases List.mem_cons.mp hA with rfl | hA
    · rw [arcs_sum_zero L v (A.vertices_subset hv) k (by
        intro C hC hvc
        exact Finset.disjoint_left.mp (hb C hC) hv hvc),add_zero]
    · have hvB : v∉B.vertices := fun hh => Finset.disjoint_left.mp (hb A hA) hh hv
      rw [B.current_zero v (A.vertices_subset hv) hvB k,ih ht hA,zero_add]

private theorem wordContour_transfer (q r : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (hw : WordContour q g w)
    (he : ∀v∈traced g w,∀k,orientedFlow q (v,k)=orientedFlow r (v,k)) :
    WordContour r g w := by
  induction w generalizing g with
  | nil => trivial
  | cons b w ih =>
    refine ⟨?_,ih (advance g b) hw.2 (fun v hv k => he v (by simp [traced,hv]) k)⟩
    intro k
    exact (he g.1 (by simp [traced]) k).symm.trans (hw.1 k)

namespace BoundaryDecomposition
variable {q : Edge M →₀ ℤ} (B : BoundaryDecomposition D q)

theorem on_arc (A : BoundaryArc D) (hA : A∈B.arcs) (v : Vertex M)
    (hv : v∈A.vertices) (k : Fin 3) : orientedFlow q (v,k)=orientedFlow A.current (v,k) := by
  have hc : v∉activeSites B.closed := fun hh => Finset.disjoint_left.mp (B.disjoint_closed A hA) hv hh
  calc
    orientedFlow q (v,k)=orientedFlow ((B.arcs.map BoundaryArc.current).sum+B.closed) (v,k) :=
      congrArg (fun r : Edge M →₀ ℤ => orientedFlow r (v,k)) B.reconstruction
    _=orientedFlow A.current (v,k) := by
      rw [map_add,Finsupp.add_apply,arcs_sum_on_member B.arcs B.pairwise A hA v hv k,
        not_active_zero B.closed v hc k,add_zero]

theorem arc_contour (A : BoundaryArc D) (hA : A∈B.arcs) : WordContour q A.start A.word :=
  wordContour_transfer A.current q A.start A.word A.contour
    (fun v hv k => (B.on_arc A hA v (List.mem_toFinset.mpr hv) k).symm)

 

theorem mem_of_contour (A : BoundaryArc D) (hc : WordContour q A.start A.word) : A∈B.arcs := by
  have hq : orientedFlow q A.start= -1 := by
    obtain ⟨b,w,hw⟩:=List.exists_cons_of_ne_nil A.nonempty
    rw [hw] at hc
    simpa only [Ne.symm (outgoingSlot_ne A.start b),ite_false,ite_true,zero_sub] using hc.1 A.start.2
  have hc0 : orientedFlow B.closed A.start=0 := by
    have hnot : (reverseGerm A.start).1∉activeSites B.closed := fun hh => A.startOutside (B.contained hh)
    have hh:=not_active_zero B.closed (reverseGerm A.start).1 hnot (reverseGerm A.start).2
    change orientedFlow B.closed (reverseGerm A.start)=0 at hh
    rw [orientedFlow_reverse] at hh
    exact neg_eq_zero.mp hh
  have hex : ∃C∈B.arcs,A.start.1∈C.vertices := by
    by_contra hh
    have hz : ∀C∈B.arcs,A.start.1∉C.vertices := by simpa only [not_exists,not_and] using hh
    have hs:=arcs_sum_zero B.arcs A.start.1 A.startInside A.start.2 hz
    have he:=congrArg (fun r : Edge M →₀ ℤ => orientedFlow r A.start) B.reconstruction
    rw [map_add,Finsupp.add_apply,hq,hc0,add_zero] at he
    change (-1 : ℤ)=orientedFlow ((B.arcs.map BoundaryArc.current).sum) (A.start.1,A.start.2) at he
    rw [hs] at he
    omega
  obtain ⟨C,hC,hv⟩:=hex
  have hCq : orientedFlow C.current A.start= -1 := (B.on_arc C hC _ hv _).symm.trans hq
  have hCr : orientedFlow C.current (reverseGerm A.start)=1 := by
    rw [orientedFlow_reverse,hCq]
    norm_num
  have ht : turnVisit C.start C.word (reverseGerm A.start)=0 :=
    turnVisit_eq_zero_of_not_mem _ _ _ _ (fun hh => A.startOutside (C.inside _ hh))
  have he : (if reverseGerm C.start=reverseGerm A.start then (1 : ℤ) else 0)-
      (if terminalGerm C.start C.word=reverseGerm A.start then 1 else 0)=1 := by
    simpa only [BoundaryArc.current,orientedFlow_arc,Finsupp.add_apply,Finsupp.sub_apply,
      Finsupp.single_apply,ht,zero_add] using hCr
  have hs : C.start=A.start := by
    have hr : reverseGerm C.start=reverseGerm A.start := by
      by_contra hh
      rw [ite_eq_right hh] at he
      split_ifs at he <;> omega
    have hh:=congrArg reverseGerm hr
    simpa using hh
  have hw : C.word=A.word := contour_open_word_unique D q A.start C.word A.word
    (hs ▸ B.arc_contour C hC) hc (hs ▸ C.inside) A.inside (hs ▸ C.endOutside) A.endOutside
  exact C.ext_data A hs hw ▸ hC

theorem arcs_unique (C : BoundaryDecomposition D q) : B.arcs.toFinset=C.arcs.toFinset := by
  ext A
  simp only [List.mem_toFinset]
  exact ⟨fun h => C.mem_of_contour A (B.arc_contour A h),fun h => B.mem_of_contour A (C.arc_contour A h)⟩
end BoundaryDecomposition
end PolynomialVacuumCylinder

end OAI

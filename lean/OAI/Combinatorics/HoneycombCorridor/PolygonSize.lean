import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Traversals

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def graphDegree (E : Finset EdgeIndex) (v : Vertex) : ℤ :=
  ∑ k : Fin 3, if edgeOf (v,k) ∈ E then 1 else 0

theorem graphDegree_incidence (E : Finset EdgeIndex) (v : Vertex) :
    graphDegree E v = ∑ e ∈ E,
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
  unfold graphDegree
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem graphDegree_sum (E : Finset EdgeIndex) :
    ∑ v ∈ edgeVertices E, graphDegree E v = 2 * (E.card : ℤ) := by
  classical
  simp_rw [graphDegree_incidence]
  rw [Finset.sum_comm]
  have he (e : EdgeIndex) (hme : e ∈ E) :
      (∑ v ∈ edgeVertices E,
        ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ)) = 2 := by
    have hu : upEnd e ∈ edgeVertices E := Finset.mem_biUnion.mpr ⟨e,hme,by simp⟩
    have hd : downEnd e ∈ edgeVertices E := Finset.mem_biUnion.mpr ⟨e,hme,by simp⟩
    rw [Finset.sum_add_distrib]
    simp [hu,hd]
  simp_rw [Finset.sum_congr rfl he]
  simp [mul_comm]

namespace Polygon

theorem degree_two (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    graphDegree P.val v = 2 := by
  classical
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  have hlocal := (simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1
  unfold graphDegree
  rw [← hw.2.2.2]
  simp_rw [local_contour_support _ (v,k) b hlocal]
  have hne := outgoingSlot_ne (v,k) b
  simp only [Fin.sum_univ_succ]
  fin_cases k <;> cases b <;> norm_num [outgoingSlot]

theorem length_eq_card_vertices (P : Polygon) : P.length = P.vertices.card := by
  have h := graphDegree_sum P.val
  change (∑ v ∈ P.vertices, graphDegree P.val v) = _ at h
  have hsum : (∑ v ∈ P.vertices, graphDegree P.val v) = 2 * (P.vertices.card : ℤ) := by
    rw [Finset.sum_congr rfl (fun v hv => P.degree_two v hv)]
    simp [mul_comm]
  rw [hsum] at h
  unfold length
  omega

theorem Traverses.length {P : Polygon} {g : Germ} {w : List Bool}
    (h : P.Traverses g w) : P.length = w.length := by
  rw [P.length_eq_card_vertices,h.vertices,List.toFinset_card_of_nodup h.2.1,traced_length]

theorem length_pos (P : Polygon) : 0 < P.length := by
  rw [P.traverses_chosen.length]
  exact List.length_pos_iff.mpr P.traversal.1

end Polygon


theorem sum_record_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (F : α × β → ℂ) :
    (∑ e ∈ s.biUnion (fun a => (t a).image (fun b => (a,b))), F e) =
      ∑ a ∈ s, ∑ b ∈ t a, F (a,b) := by
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    intro b hb c hc he
    exact (Prod.mk.inj he).2
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp hf
    exact hab ((Prod.mk.inj (hxe.trans hye.symm)).1)

theorem excursions_fibers (D : Finset Vertex) :
    excursions D = (boundaryGerms D).biUnion fun g =>
      ((leaves D g).filter fun w => (terminalGerm g w).1 ∉ D).image fun w => (g,w) := by
  classical
  ext e
  simp only [mem_excursions,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro h
    exact ⟨e.1,(mem_boundaryGerms D e.1).mpr ⟨h.1,h.2.1⟩,e.2,
      ⟨(mem_leaves_iff D e.1 e.2).mpr h.2.2.1,h.2.2.2⟩,rfl⟩
  · rintro ⟨g,hg,w,⟨hw,ht⟩,rfl⟩
    have h := (mem_boundaryGerms D g).mp hg
    exact ⟨h.1,h.2,(mem_leaves_iff _ _ _).mp hw,ht⟩

theorem firstArrivals_fibers (D : Finset Vertex) (v : Vertex) :
    firstArrivals D v = (boundaryGerms D).biUnion fun g =>
      ((leaves (D.erase v) g).filter fun w => (terminalGerm g w).1 = v).image fun w => (g,w) := by
  classical
  ext e
  simp only [mem_firstArrivals,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro h
    exact ⟨e.1,h.1,e.2,⟨(mem_leaves_iff _ _ _).mpr h.2.1,h.2.2⟩,rfl⟩
  · rintro ⟨g,hg,w,⟨hw,ht⟩,rfl⟩
    exact ⟨hg,(mem_leaves_iff _ _ _).mp hw,ht⟩

theorem boundary_marked_eq_exits (D : Finset Vertex) (g : Germ) (v : Vertex)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    markedLeaves D g v =
      ∑ w ∈ (leaves D g).filter (fun w => (terminalGerm g w).1 ∉ D),
        if v ∈ traced g w then wordWeight w else 0 := by
  classical
  have hz := (boundary_collision_cancellation D g hD hg).2 v
  unfold markedLeaves
  rw [Finset.sum_filter]
  have he : (∑ w ∈ leaves D g, if v ∈ traced g w then wordWeight w else 0) =
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∉ D then
        (if v ∈ traced g w then wordWeight w else 0) else 0) +
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases ht : (terminalGerm g w).1 ∈ D <;>
      by_cases hv : v ∈ traced g w <;> simp [ht,hv]
  rw [he,hz,add_zero]

theorem visitSum_eq_firstArrivals (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∈ D) :
    visitSum D v = ∑ e ∈ firstArrivals D v, wordWeight e.2 := by
  classical
  unfold visitSum
  rw [excursions_fibers,firstArrivals_fibers,sum_record_fibers,sum_record_fibers]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← boundary_marked_eq_exits D g v hD ((mem_boundaryGerms _ _).mp hg).2,
    markedLeaves_eq_firstArrival D g v hv]
  simp only [firstArrival,Finset.sum_filter]

theorem rayExits_eq_visitSum (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∈ D) :
    (∑ e ∈ rayExits D v, wordWeight e.2) = visitSum D v := by
  have h := prefix_ray_reversal D v hv
  rw [← visitSum_eq_firstArrivals D v hD hv] at h
  have hc := congrArg (starRingEnd ℂ) h
  simpa only [visitSum_conj,Complex.conj_conj] using hc.symm
end PolynomialVacuumBridge.Corridor

end

end OAI

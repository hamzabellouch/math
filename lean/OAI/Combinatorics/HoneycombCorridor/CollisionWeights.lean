import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionGrouping

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem IsPolygonStem.left_potential {D : Finset Vertex} {v : Vertex} {P : Polygon}
    {s : RayRecord} (hs : IsPolygonStem D v P s) :
    P.potential (leftFace (stemEnd v s)) = vertexLevel P.potential v := by
  rw [stemEnd,P.trace_left_potential _ _ hs.trace_disjoint]
  change P.potential (rightFace (v,s.1)) = _
  exact (P.off_boundary_faces v hs.1 s.1).2

theorem collision_cycle_weight (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (s c : RayRecord) (hs : s ∈ polygonStems D v P)
    (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    wordWeight (attachWord c) + wordWeight (attachWord (reverseCycle (stemEnd v s).1 c)) =
      if v ∈ P.interior then -2 * (criticalActivity : ℂ) ^ P.length else 0 := by
  classical
  have hs' := (mem_polygonStems D v P s).mp hs
  have h := (mem_cyclesAt P _ c).mp hc
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil h.1
  let g : Germ := ((stemEnd v s).1,c.1)
  have htr : P.Traverses g (b :: w) := hw ▸ h
  have he := stemGerm_eq_of_back_outside P (stemEnd v s) c.1 b w htr hs'.back_outside
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g (b :: w)
    (by simp) htr.2.1 htr.2.2.1
  have hfaces := P.interiorFaces_of_traversal g (b :: w) htr.2.1 htr.2.2.1 htr.2.2.2 p hp
  have hz : p (leftFace (stemEnd v s)) = 0 ↔ v ∉ P.interior := by
    rw [P.interior_iff_level]
    simp only [hs'.1,not_false_eq_true,true_and,not_not]
    rw [← hs'.left_potential]
    constructor
    · intro h
      apply Finsupp.notMem_support_iff.mp
      change leftFace (stemEnd v s) ∉ P.interiorFaces
      rw [hfaces]
      exact Finsupp.notMem_support_iff.mpr h
    · intro h
      apply Finsupp.notMem_support_iff.mp
      rw [← hfaces]
      exact Finsupp.notMem_support_iff.mpr h

  have hphase := collision_phase g b w p ε htr.2.1 htr.2.2.1 hp hpne hε hvals
  change stemGerm g b = stemEnd v s at he
  change wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
    if p (leftFace (stemGerm g b)) = 0 then 0 else _ at hphase
  rw [he,← htr.length] at hphase
  simp only [attachWord,hw,reverseCycle,Bool.not_not]
  rw [hphase]
  by_cases hv : v ∈ P.interior
  · rw [ite_eq_left hv,ite_eq_right (fun h => hz.mp h hv)]
  · rw [ite_eq_right hv,ite_eq_left (hz.mpr hv)]

theorem collision_cycle_sum (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (s : RayRecord) (hs : s ∈ polygonStems D v P) :
    (∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2) =
      if v ∈ P.interior then -2 * (criticalActivity : ℂ) ^ P.length * wordWeight s.2 else 0 := by
  classical
  have hs' := (mem_polygonStems D v P s).mp hs
  obtain ⟨k,w,hw⟩ := P.exists_rooted (stemEnd v s).1 hs'.2.2
  have he := (mem_cyclesAt P _ (k,w)).mpr hw
  rw [cyclesAt_eq_pair P _ (k,w) he,Finset.sum_pair (Ne.symm (reverseCycle_ne P _ (k,w) he))]
  simp only [spliceRecord,wordWeight_append]
  rw [← mul_add,collision_cycle_weight D v P s (k,w) hs he]
  split_ifs <;> ring

theorem Polygon.trace_interior_of_back (P : Polygon) (g : Germ) (w : List Bool)
    (hb : (reverseGerm g).1 ∈ P.interior)
    (hd : ∀ a ∈ traced g w, a ∉ P.vertices) :
    (∀ a ∈ traced g w, a ∈ P.interior) ∧ (reverseGerm (terminalGerm g w)).1 ∈ P.interior := by
  induction w generalizing g with
  | nil => exact ⟨by simp [traced],hb⟩
  | cons b w ih =>
      have hg : g.1 ∈ P.interior := by
        by_contra hn
        have he := P.interior_exit_on_boundary (reverseGerm g).1 g.2 hb
          (by simpa [reverseGerm] using hn)
        apply hd g.1 (by simp [traced])
        simpa [reverseGerm] using he
      have ha : (reverseGerm (advance g b)).1 ∈ P.interior := by
        simpa [advance,reverseGerm] using hg
      have hi := ih (advance g b) ha (fun a hm => hd a (List.mem_cons_of_mem _ hm))
      refine ⟨?_,hi.2⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hg
      · exact hi.1 a ha

theorem polygonStems_eq_rayExits (D : Finset Vertex) (v : Vertex) (P : Polygon)
    (hD : Filled D) (hP : P ∈ polygons D) (hv : v ∈ P.interior) :
    polygonStems D v P = rayExits P.interior v := by
  classical
  ext s
  rw [mem_polygonStems,mem_rayExits]
  have hb : (reverseGerm (rayGerm v s.1)).1 ∈ P.interior := by simpa [rayGerm,reverseGerm] using hv
  constructor
  · intro hs
    have hn := (stopped_iff_trace _ _ _).mp hs.2.1
    have hi := P.trace_interior_of_back (rayGerm v s.1) s.2 hb hs.trace_disjoint
    have ht : (stemEnd v s).1 ∉ P.interior := fun h => ((P.mem_interior _).mp h).2 hs.2.2
    refine ⟨(stopped_iff_trace _ _ _).mpr ⟨hn.1,?_,Or.inl ?_⟩,ht⟩
    · intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hn.2.1 a ha)).1,hi.1 a ha⟩
    · exact fun h => ht (Finset.mem_of_mem_erase h)
  · rintro ⟨hs,he⟩
    have hn := (stopped_iff_trace _ _ _).mp hs
    have hd : ∀ a ∈ traced (rayGerm v s.1) s.2, a ∉ P.vertices := by
      intro a ha
      exact ((P.mem_interior a).mp (Finset.mem_of_mem_erase (hn.2.1 a ha))).2
    have hi := P.trace_interior_of_back (rayGerm v s.1) s.2 hb hd
    have ht : (stemEnd v s).1 ∈ P.vertices := by
      have h := P.interior_exit_on_boundary (reverseGerm (stemEnd v s)).1 (stemEnd v s).2 hi.2
        (by simpa only [reverseGerm,neighbor_neighbor,stemEnd,rayGerm] using he)
      simpa [reverseGerm] using h
    refine ⟨((P.mem_interior v).mp hv).2,(stopped_iff_trace _ _ _).mpr ⟨hn.1,?_,Or.inl ?_⟩,ht⟩
    · intro a ha
      have hpa := hn.2.1 a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hpa).1,
        Finset.mem_sdiff.mpr ⟨hD P hP (Finset.mem_of_mem_erase hpa),hd a ha⟩⟩
    · exact fun h => (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2 ht

theorem collision_sum_polygons (D : Finset Vertex) (v : Vertex) (hD : Filled D) :
    (∑ e ∈ rayCollisions D v, wordWeight e.2) =
      ∑ P ∈ polygons D, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * visitSum P.interior v else 0 := by
  classical
  rw [collision_sum_grouped]
  apply Finset.sum_congr rfl
  intro P hP
  have hsum : (∑ s ∈ polygonStems D v P, ∑ c ∈ cyclesAt P (stemEnd v s).1,
          wordWeight (spliceRecord v s c).2) =
      ∑ s ∈ polygonStems D v P, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * wordWeight s.2 else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    exact collision_cycle_sum D v P s hs
  rw [hsum]
  by_cases hv : v ∈ P.interior
  · simp only [ite_eq_left hv]
    rw [← Finset.mul_sum,polygonStems_eq_rayExits D v P hD hP hv,
      rayExits_eq_visitSum P.interior v P.interior_filled hv]
  · simp [hv]

end PolynomialVacuumBridge.Corridor

end

end OAI

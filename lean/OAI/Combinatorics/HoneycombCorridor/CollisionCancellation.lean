import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionHistories
import OAI.Combinatorics.HoneycombCorridor.PolygonGeometry

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def polygonOfClosed (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) : Polygon :=
  ⟨(wordFlow g w).support,⟨g,w,hne,hN,hc,rfl⟩⟩

theorem polygonOfClosed_vertices (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    (polygonOfClosed g w hne hN hc).vertices = (traced g w).toFinset :=
  wordFlow_edgeVertices g w hN hc

theorem mem_traced_split (g : Germ) (w : List Bool) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ u b t, w = u ++ (b :: t) ∧ (terminalGerm g u).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with hv | hv
      · exact ⟨[],b,w,rfl,hv.symm⟩
      · obtain ⟨u,c,t,he,ht⟩ := ih (advance g b) hv
        exact ⟨b::u,c,t,by simp [he],ht⟩

theorem reverseAt_append (g : Germ) (v : Vertex) (u w : List Bool)
    (hv : v ∉ traced g u) :
    reverseAt g v (u ++ w) = u ++ reverseAt (terminalGerm g u) v w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih =>
      have hg : g.1 ≠ v := fun h => hv (by simp [traced,h])
      have ht : v ∉ traced (advance g b) u := fun h => hv (List.mem_cons_of_mem _ h)
      simp only [List.cons_append,reverseAt,ite_eq_right hg,terminalGerm,ih _ ht]

theorem split_back_not_mem (g : Germ) (u : List Bool) (b : Bool) (w : List Bool)
    (hN : (traced g (u ++ b :: w)).Nodup)
    (hg : (reverseGerm g).1 ∉ traced g (u ++ b :: w)) :
    (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: w) := by
  cases u with
  | nil => simpa only [List.nil_append,terminalGerm] using hg
  | cons c u =>
      have hm := terminal_previous_mem g (c :: u) (by simp)
      rw [traced_append] at hN
      have hd := (List.nodup_append.mp hN).2.2
      exact fun ht => hd _ hm _ ht rfl

theorem root_collision_cancels (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w))
    (hz : ∀ (P : Polygon), P.vertices = (traced g (b :: w)).toFinset →
      P.potential (leftFace g) = 0) :
    wordWeight (b :: w) + wordWeight ((!b) :: reverseTurns w) = 0 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have htr : traced t ((!b) :: w) = traced g (b :: w) := by
    change t.1 :: traced (advance t (!b)) w = _
    rw [ha,hc]
    rfl
  have hNt : (traced t ((!b) :: w)).Nodup := htr ▸ hN
  have hct : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = _
    rw [ha]
    rfl
  let P := polygonOfClosed t ((!b) :: w) (by simp) hNt hct
  have hPv : P.vertices = (traced g (b :: w)).toFinset := by
    rw [polygonOfClosed_vertices,htr]
  have hPz := hz P hPv
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ :=
    simple_closed_word_indicator t ((!b) :: w) (by simp) hNt hct
  have hPs := P.interiorFaces_of_traversal t ((!b) :: w) hNt hct rfl p hp
  have hpz : p (leftFace g) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [← hPs]
    exact Finsupp.notMem_support_iff.mpr hPz
  have hr := collision_phase t (!b) w p ε hNt hct hp hpne hε hvals
  have he : (t.1,unusedSlot t (!b)) = g := hs
  simp only [Bool.not_not,he,hpz,ite_eq_left] at hr
  exact hr

theorem boundary_collision_pair (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D)
    (hw : w ∈ leaves D g) (ht : (terminalGerm g w).1 ∈ D) :
    wordWeight w + wordWeight (collisionReverse g w) = 0 := by
  have hstop := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hmem : (terminalGerm g w).1 ∈ traced g w :=
    hstop.2.2.resolve_left (not_not.mpr ht)
  obtain ⟨u,b,t,rfl,hroot⟩ := mem_traced_split g w (terminalGerm g w).1 hmem
  have hN := hstop.1
  rw [traced_append] at hN
  have hna := List.nodup_append.mp hN
  have hb : (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: t) :=
    split_back_not_mem g u b t hstop.1 (fun h => hg (hstop.2.1 _ h))
  have hct : (terminalGerm (terminalGerm g u) (b :: t)).1 = (terminalGerm g u).1 := by
    rw [← terminalGerm_append]
    exact hroot.symm
  have hzero : wordWeight (b :: t) + wordWeight ((!b) :: reverseTurns t) = 0 := by
    apply root_collision_cancels (terminalGerm g u) b t hna.2.1 hct hb
    intro P hPv
    have hPD : P ∈ polygons D := by
      apply (mem_polygons D P).mpr
      rw [hPv]
      intro v hv
      exact hstop.2.1 v (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp hv))
    have hdis : ∀ v ∈ traced g u, v ∉ P.vertices := by
      intro v hv hm
      rw [hPv,List.mem_toFinset] at hm
      exact hna.2.2 _ hv _ hm rfl
    rw [P.trace_left_potential g u hdis]
    exact P.outside_port_potential D hD hPD g hg
  have hnot : (terminalGerm g (u ++ b :: t)).1 ∉ traced g u := by
    intro hm
    apply hna.2.2 _ hm _ _ rfl
    rw [← hroot]
    simp [traced]
  unfold collisionReverse
  rw [reverseAt_append g _ u (b :: t) hnot]
  have he : (terminalGerm g u).1 = (terminalGerm g (u ++ b :: t)).1 := hroot
  simp only [reverseAt,ite_eq_left he,wordWeight_append]
  rw [← mul_add,hzero,mul_zero]

private theorem collision_subsum_zero (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) (S : Finset (List Bool))
    (hS : ∀ w ∈ S, w ∈ leaves D g ∧ (terminalGerm g w).1 ∈ D)
    (hrev : ∀ w ∈ S, collisionReverse g w ∈ S) :
    (∑ w ∈ S, wordWeight w) = 0 := by
  apply Finset.sum_involution (fun w _ => collisionReverse g w)
  · intro w hw
    exact boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
  · intro w hw hn he
    apply hn
    have h := boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
    rw [he] at h
    linear_combination (1 / 2 : ℂ) * h
  · exact hrev
  · intro w hw
    exact (collisionReverse_leaf D g w (hS w hw).1 hg (hS w hw).2).2.2.2

theorem boundary_collision_cancellation (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    collisionSum D g = 0 ∧ ∀ v : Vertex,
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) = 0 := by
  classical
  constructor
  · unfold collisionSum
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      exact Finset.mem_filter.mp hw
    · intro w hw
      obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩
  · intro v
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      have h := Finset.mem_filter.mp hw
      exact ⟨h.1,h.2.1⟩
    · intro w hw
      obtain ⟨hw,ht,hv⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1,(h.2.2.1 v).mpr hv⟩
end PolynomialVacuumBridge.Corridor

end

end OAI

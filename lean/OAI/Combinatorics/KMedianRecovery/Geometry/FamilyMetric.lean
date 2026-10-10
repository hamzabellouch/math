import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestImage
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestMap
import OAI.Combinatorics.KMedianRecovery.Recovery.PhasesBounded

namespace OAI

namespace MetricKMedianRecovery.FreshCopyEndpoints
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

@[instance_reducible]
noncomputable def familyMetric (i : X) : PseudoMetricSpace (X ⊕ ℝ) :=
  LeafMetric.attachedMetric (fun _ : ℝ => i) (fun s => max s 0) (fun _ => le_max_right _ _)

omit [PseudoMetricSpace X] [DecidableEq X] in
def incl : X ↪ X ⊕ ℝ := ⟨Sum.inl,Sum.inl_injective⟩

omit [Fintype D] [DecidableEq X] in
lemma original_dist (i x y : X) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    dist (incl x) (incl y) = dist x y := by
  exact LeafMetric.original_distance (fun _ : ℝ => i) (fun s => max s 0) x y

omit [Fintype D] [DecidableEq X] in
lemma leaf_dist (i x : X) (s : ℝ) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    dist (incl x) (Sum.inr s) = dist x i+max s 0 := by
  exact LeafMetric.copy_distance (fun _ : ℝ => i) (fun s => max s 0) x s

omit [Fintype D] [PseudoMetricSpace X] in
lemma fresh (F B : Finset X) (s : ℝ) : Sum.inr s ∉ F.image incl ∪ B.image incl := by
  simp [incl]

theorem zero_endpoint (loc : D → X) (F B : Finset X) (v lam eta zEnd : ℝ)
    (i : X) (hiF : i ∈ F) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (T : List (List X)) (hh : History loc F B v lam eta 0 ∅ T)
    (hiQ : i ∈ after ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) zEnd (after ∅ T) j) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∃ T' : List (List (X ⊕ ℝ)), T'.length = T.length ∧
      History (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr 0) (B.image incl))
        v lam eta 0 ∅ T' ∧
      (∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) zEnd (after ∅ T') j) ∧
      ((after ∅ T) ∩ F).card = ((after ∅ T') ∩ F.image incl).card+1 ∧
      ((after ∅ T') \ F.image incl).card = ((after ∅ T) \ F).card+1 ∧
      (∀ j, nearestDistance (incl (loc j)) (after ∅ T') = nearestDistance (loc j) (after ∅ T)) := by
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  let U := T.map (List.map (incl : X ↪ X ⊕ ℝ))
  have hr : ∀ x y : X, dist (incl x) (incl y) = dist x y := original_dist i
  have hU : History (fun j => incl (loc j)) (F.image incl) (B.image incl) v lam eta 0 ∅ U := by
    simpa only [Finset.image_empty] using HistoryIsometry.history_map incl hr loc F B ∅ v lam eta 0 T hh
  have hafter : after ∅ U = (after ∅ T).image incl := by
    simpa only [Finset.image_empty] using HistoryIsometry.after_map incl (∅ : Finset X) T
  have hd : ∀ j, dist (incl (loc j)) (incl i) = dist (incl (loc j)) (Sum.inr 0) := by
    intro j
    rw [hr,leaf_dist i, max_self,add_zero]
  have hUi : incl i ∈ after ∅ U := by
    rw [hafter]
    exact Finset.mem_image.mpr ⟨i,hiQ,rfl⟩
  have hUiF : incl i ∈ F.image incl := Finset.mem_image.mpr ⟨i,hiF,rfl⟩
  have hUt : ∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) zEnd (after ∅ U) j := by
    intro j hj
    rw [hafter] at hj
    exact hterm j ((HistoryIsometry.active_map incl hr loc (1-3*v) zEnd (after ∅ T) j).mp hj)
  obtain ⟨hvalid,hterminal,hpaid,hfree⟩ := CoincidentHistory.endpoint (fun j => incl (loc j))
    (F.image incl) (B.image incl) v lam eta zEnd (incl i) (Sum.inr 0) hUiF (fresh F B 0)
    hd ht hlam U hU hUi hUt
  let T' := U.map (List.map (Equiv.swap (incl i) (Sum.inr (0:ℝ))))
  refine ⟨T',?_,hvalid,hterminal,?_,?_,?_⟩
  · simp only [T',U,List.length_map]
  · rw [hafter,HistoryIsometry.paid_map] at hpaid
    exact hpaid
  · rw [hafter,HistoryIsometry.free_map] at hfree
    exact hfree
  · intro j
    have hs : after ∅ T' = (after ∅ U).image (Equiv.swap (incl i) (Sum.inr (0:ℝ))) := by
      simpa only [Finset.image_empty] using
        PhaseHistoryTransfer.after_map (∅ : Finset (X ⊕ ℝ)) U (Equiv.swap (incl i) (Sum.inr (0:ℝ)))
    rw [hs,CoincidentHistory.nearest_image (fun j => incl (loc j)) (after ∅ U)
      (Equiv.swap (incl i) (Sum.inr (0:ℝ)))
      (CoincidentHistory.swap_distances (fun j => incl (loc j)) (incl i) (Sum.inr 0) hd),
      hafter,HistoryIsometry.nearest_map incl hr]

omit [Fintype D] in
lemma live_map {Y : Type*} [PseudoMetricSpace Y] [DecidableEq Y]
    (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (v : ℝ) (q : ℕ) (Q : Finset X) (T : List (List X))
    (h : HistoryPhaseBound.Live loc v q Q T) :
    HistoryPhaseBound.Live (fun j => r (loc j)) v q (Q.image r) (T.map (List.map r)) := by
  induction T generalizing q Q with
  | nil => trivial
  | cons H T ih =>
    change (∃ j, activeAt loc (1-3*v) ((1+v^2)^q) Q j) ∧ _ at h
    change (∃ j, activeAt (fun j => r (loc j)) (1-3*v) ((1+v^2)^q) (Q.image r) j) ∧ _
    refine ⟨?_,?_⟩
    · obtain ⟨j,hj⟩ := h.1
      exact ⟨j,(HistoryIsometry.active_map r hr loc (1-3*v) ((1+v^2)^q) Q j).mpr hj⟩
    · rw [HistoryIsometry.image_union]
      exact ih (q+1) (Q ∪ H.toFinset) h.2

theorem disabling_endpoint (loc : D → X) (F B : Finset X) (v lam M eta : ℝ)
    (N : ℕ) (i : X) (hiF : i ∈ F) (H : List X) (T : List (List X))
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hMpos : 0 < M) (hN : 3 ≤ N) (hprice : lam ≤ 8*N*M)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hsep : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (hh : History loc F B v lam eta 0 ∅ (H::T))
    (hlive : HistoryPhaseBound.Live loc v 0 ∅ (H::T))
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(H::T).length) (after ∅ (H::T)) j) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∃ T' : List (List (X ⊕ ℝ)), T'.length = (H::T).length ∧
      History (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr (20*N*M)) (B.image incl))
        v lam eta 0 ∅ T' ∧
      (∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) ((1+v^2)^T'.length) (after ∅ T') j) ∧
      ((after ∅ T') ∩ F.image incl).card = ((after ∅ (H::T)) ∩ F).card ∧
      ((after ∅ T') \ F.image incl).card = ((after ∅ (H::T)) \ F).card+1 ∧
      (∀ j, nearestDistance (incl (loc j)) (after ∅ T') = nearestDistance (loc j) (after ∅ (H::T))) := by
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  let U := (H::T).map (List.map (incl : X ↪ X ⊕ ℝ))
  let f : X ⊕ ℝ := Sum.inr (20*N*M)
  have hr : ∀ x y : X, dist (incl x) (incl y) = dist x y := original_dist i
  have hF : (F.image (incl : X ↪ X ⊕ ℝ)).Nonempty :=
    ⟨incl i,Finset.mem_image.mpr ⟨i,hiF,rfl⟩⟩
  have hU : History (fun j => incl (loc j)) (F.image incl) (B.image incl) v lam eta 0 ∅ U := by
    simpa only [Finset.image_empty] using HistoryIsometry.history_map incl hr loc F B ∅ v lam eta 0 (H::T) hh
  have hafter : after ∅ U = (after ∅ (H::T)).image incl := by
    simpa only [Finset.image_empty] using HistoryIsometry.after_map incl (∅ : Finset X) (H::T)
  have hUt : ∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) ((1+v^2)^U.length) (after ∅ U) j := by
    intro j hj
    rw [hafter] at hj
    simp only [U,List.length_map] at hj
    exact hterm j ((HistoryIsometry.active_map incl hr loc (1-3*v)
      ((1+v^2)^(H::T).length) (after ∅ (H::T)) j).mp hj)
  have hUl : HistoryPhaseBound.Live (fun j => incl (loc j)) v 0 ∅ U := by
    simpa only [Finset.image_empty] using live_map incl hr loc v 0 ∅ (H::T) hlive
  have hM' : ∀ x ∈ F.image (incl : X ↪ X ⊕ ℝ), ∀ j, dist x (incl (loc j)) ≤ M := by
    intro x hx j
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    subst x
    rw [hr]
    exact hM y hy j
  have hsep' : ∀ j x, x ∈ F.image (incl : X ↪ X ⊕ ℝ) → 1 ≤ dist x (incl (loc j)) := by
    intro j x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    subst x
    rw [hr]
    exact hsep j y hy
  have hfar : ∀ j, 20*N*M ≤ dist (incl (loc j)) f := by
    intro j
    change 20*N*M ≤ dist (incl (loc j)) (Sum.inr (20*N*M))
    rw [leaf_dist i,max_eq_left (by positivity : (0:ℝ) ≤ 20*N*M)]
    linarith only [dist_nonneg (x := loc j) (y := i)]
  obtain ⟨hvalid,hterminal,hpaid,hfree⟩ := UniformDisablingEndpoint.endpoint
    (fun j => incl (loc j)) (F.image incl) (B.image incl) hF v lam M eta N
    (H.map incl) (T.map (List.map incl)) f hv hvsmall hlam hMpos hN hprice
    hM' hsep' (fresh F B (20*N*M)) hfar hU hUl hUt
  let T' := (f::H.map incl)::T.map (List.map incl)
  refine ⟨T',?_,hvalid,hterminal,?_,?_,?_⟩
  · simp only [T',List.length_cons,List.length_map]
  · change (after ∅ T' ∩ F.image incl).card = (after ∅ U ∩ F.image incl).card at hpaid
    rw [hafter,HistoryIsometry.paid_map] at hpaid
    exact hpaid
  · change (after ∅ T' \ F.image incl).card = (after ∅ U \ F.image incl).card+1 at hfree
    rw [hafter,HistoryIsometry.free_map] at hfree
    exact hfree
  · intro j
    have hs : after ∅ T' = insert f (after ∅ U) := by
      simp only [T',U,List.map_cons,after,List.toFinset_cons,Finset.union_insert,DisablingHistory.after_insert]
    have hend : ∀ j, (1+v^2)^U.length < (1-3*v)*dist (incl (loc j)) f := by
      intro a
      have hb := UniformDisablingEndpoint.uniform_far (fun j => incl (loc j))
        (F.image incl) (B.image incl) hF v lam M eta N U f hv hvsmall hlam
        hMpos hN hprice hM' hsep' hfar hU hUl T.length (by simp [U]) a
      simpa only [U,List.length_map,List.length_cons,Nat.zero_add,pow_succ,mul_comm] using hb
    have he := DisablingCopy.inactive_distance (fun j => incl (loc j)) (1-3*v)
      ((1+v^2)^U.length) (after ∅ U) f (by linarith only [hvsmall]) hend j (hUt j)
    have ht : (1-3*v) ≠ 0 := by linarith only [hvsmall]
    have he' := mul_left_cancel₀ ht he
    rw [hs,he',hafter,HistoryIsometry.nearest_map incl hr]

end MetricKMedianRecovery.FreshCopyEndpoints

end OAI

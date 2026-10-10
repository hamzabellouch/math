import OAI.NumberTheory.Ostmann.Tree.IncidenceCycleSigns

namespace OAI

/-! # A simple cycle moves at most two leaves in each quartet -/

namespace Ostmann

open scoped BigOperators

theorem incidenceDart_positive_target {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart)
    (hd : incidenceDartSign d = 1) :
    d.snd = Sum.inr (quartet (incidenceDartLabel component quartet d)) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨_, hsnd⟩ | ⟨hfst, _⟩
  · exact hsnd
  · simp [incidenceDartSign, hfst] at hd

theorem incidenceDart_negative_source {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart)
    (hd : incidenceDartSign d = -1) :
    d.fst = Sum.inr (quartet (incidenceDartLabel component quartet d)) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, _⟩ | ⟨hfst, _⟩
  · simp [incidenceDartSign, hfst] at hd
  · exact hfst

theorem exists_dart_of_incidenceWalkSign_ne_zero {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (i : L)
    (hi : incidenceWalkSign component quartet w i ≠ 0) :
    ∃ d ∈ w.darts, incidenceDartLabel component quartet d = i := by
  by_contra h
  apply hi
  apply list_label_sum_eq_zero
  simpa only [List.mem_map, not_exists, not_and] using h

theorem incidenceCycle_positive_unique {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle)
    (i j : L) (hi : incidenceWalkSign component quartet w i = 1)
    (hj : incidenceWalkSign component quartet w j = 1) (hq : quartet i = quartet j) : i = j := by
  obtain ⟨d, hd, hdi⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w i
    (by rw [hi]; norm_num)
  obtain ⟨e, he, hej⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w j
    (by rw [hj]; norm_num)
  have hds : incidenceDartSign d = 1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet d) = _ at h
    rw [hdi, hi] at h
    exact h.symm
  have hes : incidenceDartSign e = 1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) e he
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet e) = _ at h
    rw [hej, hj] at h
    exact h.symm
  have hnd : (w.darts.map (fun d => d.snd)).Nodup := by
    rw [SimpleGraph.Walk.map_snd_darts]
    exact hw.support_nodup
  have hde : d = e := List.inj_on_of_nodup_map hnd hd he (by
    rw [incidenceDart_positive_target component quartet d hds,
      incidenceDart_positive_target component quartet e hes, hdi, hej, hq])
  exact hdi.symm.trans ((congrArg (incidenceDartLabel component quartet) hde).trans hej)

theorem incidenceCycle_negative_unique {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle)
    (i j : L) (hi : incidenceWalkSign component quartet w i = -1)
    (hj : incidenceWalkSign component quartet w j = -1) (hq : quartet i = quartet j) : i = j := by
  obtain ⟨d, hd, hdi⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w i
    (by rw [hi]; norm_num)
  obtain ⟨e, he, hej⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w j
    (by rw [hj]; norm_num)
  have hds : incidenceDartSign d = -1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet d) = _ at h
    rw [hdi, hi] at h
    exact h.symm
  have hes : incidenceDartSign e = -1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) e he
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet e) = _ at h
    rw [hej, hj] at h
    exact h.symm
  have hnd : (w.darts.map (fun d => d.fst)).Nodup := by
    rw [SimpleGraph.Walk.map_fst_darts]
    exact hw.nodup_dropLast_support
  have hde : d = e := List.inj_on_of_nodup_map hnd hd he (by
    rw [incidenceDart_negative_source component quartet d hds,
      incidenceDart_negative_source component quartet e hes, hdi, hej, hq])
  exact hdi.symm.trans ((congrArg (incidenceDartLabel component quartet) hde).trans hej)

theorem incidenceCycle_quartet_support_card_le_two {L C Q : Type*}
    [Fintype L] [DecidableEq L] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle) (q : Q) :
    (Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i ≠ 0)).card ≤ 2 := by
  let s := Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i = 1)
  let t := Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i = -1)
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    obtain ⟨hiQ, hiS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjQ, hjS⟩ := (Finset.mem_filter.mp hj).2
    exact incidenceCycle_positive_unique component quartet w hw i j hiS hjS (hiQ.trans hjQ.symm))
  have ht : t.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    obtain ⟨hiQ, hiS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjQ, hjS⟩ := (Finset.mem_filter.mp hj).2
    exact incidenceCycle_negative_unique component quartet w hw i j hiS hjS (hiQ.trans hjQ.symm))
  have hsub : Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i ≠ 0) ⊆ s ∪ t := by
    intro i hi
    obtain ⟨hiq, hin⟩ := (Finset.mem_filter.mp hi).2
    rcases incidenceWalkSign_values component quartet w hw.isTrail i with h0 | h1 | hm
    · exact (hin h0).elim
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiq, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiq, hm⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

/-- The exact combinatorial data required by the quartet projection. -/
structure BalancedIncidenceCycle {L C Q : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) where
  sign : L → ℤ
  nonzero : ∃ i, sign i = 1 ∨ sign i = -1
  values : ∀ i, sign i = 0 ∨ sign i = 1 ∨ sign i = -1
  component_balanced : ∀ c, (∑ i ∈ Finset.univ.filter (fun i => component i = c), sign i) = 0
  quartet_balanced : ∀ q, (∑ i ∈ Finset.univ.filter (fun i => quartet i = q), sign i) = 0
  quartet_support : ∀ q,
    (Finset.univ.filter (fun i => quartet i = q ∧ sign i ≠ 0)).card ≤ 2

theorem exists_balancedIncidenceCycle {L C Q : Type*}
    [Fintype L] [Fintype C] [Fintype Q] [Nonempty L]
    [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q)
    (hcard : Fintype.card C + Fintype.card Q ≤ Fintype.card L) :
    Nonempty (BalancedIncidenceCycle component quartet) := by
  rcases incidence_parallel_or_cycle component quartet hcard with ⟨i, j, hij, hc, hq⟩ | ⟨v, w, hw⟩
  · refine ⟨{
      sign := parallelCycleSign i j
      nonzero := ⟨i, Or.inl (parallelCycleSign_left i j hij)⟩
      values := ?_
      component_balanced := parallelCycleSign_balanced component i j hc
      quartet_balanced := parallelCycleSign_balanced quartet i j hq
      quartet_support := ?_
    }⟩
    · intro k
      by_cases hki : k = i
      · subst k; exact Or.inr (Or.inl (parallelCycleSign_left i j hij))
      by_cases hkj : k = j
      · subst k; exact Or.inr (Or.inr (parallelCycleSign_right i j hij))
      exact Or.inl (parallelCycleSign_other i j k hki hkj)
    · intro q
      have hsub : Finset.univ.filter (fun k => quartet k = q ∧ parallelCycleSign i j k ≠ 0) ⊆ {i, j} := by
        intro k hk
        have hn := (Finset.mem_filter.mp hk).2.2
        by_cases hki : k = i
        · simp [hki]
        by_cases hkj : k = j
        · simp [hkj]
        exact (hn (parallelCycleSign_other i j k hki hkj)).elim
      exact (Finset.card_le_card hsub).trans (by simp [hij])
  · exact ⟨{
      sign := incidenceWalkSign component quartet w
      nonzero := incidenceCycleSign_nonzero component quartet w hw
      values := incidenceWalkSign_values component quartet w hw.isTrail
      component_balanced := incidenceWalkSign_component_balanced component quartet w
      quartet_balanced := incidenceWalkSign_quartet_balanced component quartet w
      quartet_support := incidenceCycle_quartet_support_card_le_two component quartet w hw
    }⟩

theorem BalancedIncidenceCycle.preserves_component_products {L C Q G : Type*}
    [Fintype L] [DecidableEq L] [DecidableEq C] [DecidableEq Q] [CommGroup G]
    {component : L → C} {quartet : L → Q}
    (cycle : BalancedIncidenceCycle component quartet) (z : G) (m : L → G) (c : C) :
    (∏ i ∈ Finset.univ.filter (fun i => component i = c), cycleMultiply cycle.sign z m i) =
      ∏ i ∈ Finset.univ.filter (fun i => component i = c), m i :=
  cycleMultiply_preserves_product _ _ (cycle.component_balanced c) z m

theorem BalancedIncidenceCycle.preserves_quartet_products {L C Q G : Type*}
    [Fintype L] [DecidableEq L] [DecidableEq C] [DecidableEq Q] [CommGroup G]
    {component : L → C} {quartet : L → Q}
    (cycle : BalancedIncidenceCycle component quartet) (z : G) (m : L → G) (q : Q) :
    (∏ i ∈ Finset.univ.filter (fun i => quartet i = q), cycleMultiply cycle.sign z m i) =
      ∏ i ∈ Finset.univ.filter (fun i => quartet i = q), m i :=
  cycleMultiply_preserves_product _ _ (cycle.quartet_balanced q) z m

end Ostmann

end OAI

import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedSubcollection
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathProfiles
import Mathlib.Data.List.OfFn

namespace OAI

/-! Labelled subcollections of actual assigned paths, with their exact
amount and number of paths. Labels distinguish paths of equal length. -/

namespace CycleClique.Construction
open scoped BigOperators Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

namespace SystemAssignedAmounts

theorem of_profiles {C : List (List V)} {P : List (List ℕ)}
    (h : List.Forall₂ (AssignedAmounts Q) C P) :
    SystemAssignedAmounts Q C P.flatten := by
  induction h with
  | nil => exact .nil
  | cons hh ht ih => exact .cons hh ih

theorem realize_labels (S : RawPathSystem G Q) {ι : Type*}
    (labels : List ι) (wt : ι → ℕ) (hnodup : labels.Nodup)
    (h : SystemAssignedAmounts Q S.chains (labels.map wt))
    (J : Finset ι) (hJ : J ⊆ labels.toFinset) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card := by
  classical
  let K := labels.filter (fun i => decide (i ∈ J))
  have hKnodup : K.Nodup := hnodup.filter _
  have hKset : K.toFinset = J := by
    ext i
    simp only [K, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hi => ⟨List.mem_toFinset.mp (hJ hi), hi⟩⟩
  have hsub : (K.map wt).Sublist (labels.map wt) := (List.filter_sublist).map wt
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist S hsub
  refine ⟨T, ?_, ?_⟩
  · have hs := List.sum_toFinset wt hKnodup
    rw [hKset] at hs
    exact hTa.trans hs.symm
  · rw [hTe, List.length_map, ← List.toFinset_card_of_nodup hKnodup, hKset]


theorem realize_sublist_of_perm (S : RawPathSystem G Q) {w u v : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hp : w.Perm u) (hs : v.Sublist u) :
    ∃ T : ExpandedPathSystem G Q, T.amount = v.sum ∧ T.assignedCount = v.length := by
  obtain ⟨v', hvp, hvs⟩ := List.exists_perm_sublist hs hp.symm
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist S hvs
  exact ⟨T, hTa.trans hvp.sum_eq, hTe.trans hvp.length_eq⟩

theorem realize_labels_of_perm (S : RawPathSystem G Q) {ι : Type*}
    {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (labels : List ι) (wt : ι → ℕ) (hnodup : labels.Nodup)
    (hp : w.Perm (labels.map wt)) (J : Finset ι) (hJ : J ⊆ labels.toFinset) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card := by
  classical
  let K := labels.filter (fun i => decide (i ∈ J))
  have hKnodup : K.Nodup := hnodup.filter _
  have hKset : K.toFinset = J := by
    ext i
    simp only [K, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hi => ⟨List.mem_toFinset.mp (hJ hi), hi⟩⟩
  have hsub : (K.map wt).Sublist (labels.map wt) := (List.filter_sublist).map wt
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist_of_perm S hp hsub
  refine ⟨T, ?_, ?_⟩
  · have hs := List.sum_toFinset wt hKnodup
    rw [hKset] at hs
    exact hTa.trans hs.symm
  · rw [hTe, List.length_map, ← List.toFinset_card_of_nodup hKnodup, hKset]

theorem labelled_fin_range (S : RawPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) :
    ∃ wt : Fin w.length → ℕ,
      (∀ i, 0 < wt i) ∧ (∑ i, wt i) = S.amount ∧
      (∀ J : Finset (Fin w.length), ∃ T : ExpandedPathSystem G Q,
        T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) := by
  classical
  let wt : Fin w.length → ℕ := w.get
  have hmap : (List.finRange w.length).map wt = w := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get w
  have hlabels : SystemAssignedAmounts Q S.chains ((List.finRange w.length).map wt) := by
    rw [hmap]
    exact h
  refine ⟨wt, ?_, ?_, ?_⟩
  · intro i
    exact h.positive (wt i) (List.get_mem w i)
  · have hs := List.sum_toFinset wt (List.nodup_finRange w.length)
    have hset : (List.finRange w.length).toFinset = Finset.univ := by ext i; simp
    rw [hset, hmap] at hs
    rw [hs, h.sum_eq, ← S.amount_eq_outside_count]
  · intro J
    exact hlabels.realize_labels S _ wt (List.nodup_finRange w.length) J (by intro i hi; simp only [List.mem_toFinset, List.mem_finRange])

end SystemAssignedAmounts

namespace RawPathSystem

theorem exists_labelled_amounts (S : RawPathSystem G Q) :
    ∃ e : ℕ, ∃ wt : Fin e → ℕ,
      e = S.assignedCount ∧ (∀ i, 0 < wt i) ∧ (∑ i, wt i) = S.amount ∧
      (∀ J : Finset (Fin e), ∃ T : ExpandedPathSystem G Q,
        T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) := by
  obtain ⟨w, h⟩ := SystemAssignedAmounts.exists_of_raw S
  obtain ⟨wt, hpos, hsum, hreal⟩ := h.labelled_fin_range S
  exact ⟨w.length, wt, h.length_eq, hpos, hsum, hreal⟩

end RawPathSystem

end CycleClique.Construction

end OAI

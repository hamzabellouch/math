import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBoundsAllSeeds

namespace OAI

/-! Exact candidate pruning uses value lower bounds, without an accuracy event. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_filter_map {ι : Type*} (indices : List ι) (keep : ι → Bool)
    (value : ι → ℚ) (fallback : ℚ)
    (hdiscard : ∀ i ∈ indices, keep i = false → fallback ≤ value i) :
    rationalMinimum fallback ((indices.filter keep).map value) =
      rationalMinimum fallback (indices.map value) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hrest : ∀ j ∈ rest, keep j = false → fallback ≤ value j :=
      fun j hj => hdiscard j (List.mem_cons.mpr (Or.inr hj))
    cases hp : keep i with
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, rationalMinimum]
      rw [ih hrest]
      exact (min_eq_right ((rationalMinimum_le_fallback _ _).trans
        (hdiscard i (List.mem_cons_self) hp))).symm
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, rationalMinimum, ih hrest]

theorem rationalMinimum_local_complete {ι : Type*} (complete nearby : List ι)
    (value : ι → ℚ) (fallback : ℚ)
    (hsubset : ∀ i ∈ nearby, i ∈ complete)
    (hcover : ∀ i ∈ complete, value i ≤ fallback → i ∈ nearby) :
    rationalMinimum fallback (nearby.map value) = rationalMinimum fallback (complete.map value) := by
  apply le_antisymm
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    by_cases hvalue : value i ≤ fallback
    · exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hcover i hi hvalue, rfl⟩)
    · exact (rationalMinimum_le_fallback _ _).trans (le_of_not_ge hvalue)
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hsubset i hi, rfl⟩)

theorem rationalMinimum_min_fallback (a b : ℚ) (values : List ℚ) :
    min a (rationalMinimum b values) = rationalMinimum (min a b) values := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
    simp only [rationalMinimum, ← ih]
    exact min_left_comm _ _ _

theorem rationalMinimum_local_complete_lt {ι : Type*} (complete nearby : List ι)
    (value : ι → ℚ) (fallback : ℚ)
    (hsubset : ∀ i ∈ nearby, i ∈ complete)
    (hcover : ∀ i ∈ complete, value i < fallback → i ∈ nearby) :
    rationalMinimum fallback (nearby.map value) = rationalMinimum fallback (complete.map value) := by
  apply le_antisymm
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    by_cases hvalue : value i < fallback
    · exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hcover i hi hvalue, rfl⟩)
    · exact (rationalMinimum_le_fallback _ _).trans (le_of_not_gt hvalue)
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hsubset i hi, rfl⟩)

theorem rationalMinimum_cons_fallback (fallback v : ℚ) (values : List ℚ) :
    rationalMinimum fallback (v :: values) = min fallback (rationalMinimum v values) := by
  change min v (rationalMinimum fallback values) = _
  rw [rationalMinimum_min_fallback, rationalMinimum_min_fallback, min_comm v fallback]

theorem rationalMinimum_map_max (lower fallback : ℚ) (values : List ℚ) :
    rationalMinimum (max lower fallback) (values.map (max lower)) =
      max lower (rationalMinimum fallback values) := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, rationalMinimum, ih, max_min_distrib_left]

theorem rationalRefinementUpdate_online_list (delta cone : ℚ) (values : List ℚ) :
    rationalRefinementUpdate delta cone (rationalOnlineMinimum values) =
      rationalMinimum cone (values.map (max (cone / (1 + delta)))) := by
  cases values with
  | nil => rfl
  | cons v rest =>
    simp only [rationalOnlineMinimum, rationalRefinementUpdate, List.map_cons,
      rationalMinimum_cons_fallback, rationalMinimum_map_max]

theorem rationalRefinementUpdate_filter_online {ι : Type*}
    (indices : List ι) (keep : ι → Bool) (value : ι → ℚ) (delta cone : ℚ)
    (hdiscard : ∀ i ∈ indices, keep i = false → cone ≤ value i) :
    rationalRefinementUpdate delta cone (rationalOnlineMinimum ((indices.filter keep).map value)) =
      rationalRefinementUpdate delta cone (rationalOnlineMinimum (indices.map value)) := by
  simp only [rationalRefinementUpdate_online_list, List.map_map, Function.comp_def]
  apply rationalMinimum_filter_map
  intro i hi hkeep
  exact (hdiscard i hi hkeep).trans (le_max_right _ _)

theorem rationalActionValue_pruned_lower {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ) (q : Parent)
    (action : RationalBellmanAction Parent Child M) (threshold : ℚ)
    (hcharge : threshold ≤ L * distance q action.center)
    (hconnection : 0 ≤ action.connection) (hchild : ∀ i, 0 ≤ child (action.childState i)) :
    threshold ≤ rationalActionValue distance L child q action := by
  unfold rationalActionValue
  apply hcharge.trans
  simpa only [add_assoc] using
    (le_add_of_nonneg_right (a := L * distance q action.center)
      (add_nonneg hconnection (sum_nonneg fun i _ => hchild i)))

theorem rationalBellman_prune_centers {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ) (q : Parent)
    (hconnection : ∀ action ∈ actions, 0 ≤ action.connection) (hchild : ∀ s, 0 ≤ child s) :
    rationalBellman fallback distance L
        (actions.filter (fun action => decide (L * distance q action.center ≤ fallback q))) child q =
      rationalBellman fallback distance L actions child q := by
  unfold rationalBellman
  apply rationalMinimum_filter_map
  intro action ha hkeep
  have hfar : ¬ L * distance q action.center ≤ fallback q := of_decide_eq_false hkeep
  exact rationalActionValue_pruned_lower distance L child q action (fallback q)
    (le_of_lt (lt_of_not_ge hfar)) (hconnection action ha) (fun i => hchild _)

end EditApproximation

end OAI

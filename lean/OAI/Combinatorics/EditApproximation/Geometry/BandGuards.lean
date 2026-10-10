import OAI.Combinatorics.EditApproximation.Geometry.ComparisonBandCoverage

namespace OAI

/-!
# Literal band endpoint geometry and rounding guards

The full child endpoint diameter follows from the computed internal cuts
and zero connection, including the two outside endpoints.
-/

namespace EditApproximation

open Finset

theorem connectionBudget_zero_head {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0) :
    (states.head?.map TargetInterval.lo).getD start = start := by
  cases states with
  | nil => rfl
  | cons state rest =>
    have hdistance : Nat.dist start state.lo = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    exact (Nat.eq_of_dist_eq_zero hdistance).symm

/-- Each actual right endpoint is the next actual left endpoint, or the
parent's end when this is the last child. -/
theorem connectionBudget_zero_right {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0)
    (i : ℕ) (hi : i < states.length) :
    states[i].hi = connectionPrefixBoundary states finish (i + 1) := by
  induction states generalizing start i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons state rest ih =>
    have htail : connectionBudget state.hi rest finish = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    cases i with
    | zero =>
      cases rest with
      | nil =>
        exact Nat.eq_of_dist_eq_zero htail
      | cons next rest =>
        have hdistance : Nat.dist state.hi next.lo = 0 := by
          change Nat.dist state.hi next.lo + connectionBudget next.hi rest finish = 0 at htail
          omega
        exact Nat.eq_of_dist_eq_zero hdistance
    | succ i =>
      have hprev := ih state.hi htail i (by simp only [List.length_cons] at hi; omega)
      simpa only [List.getElem_cons_succ, connectionPrefixBoundary, List.drop_succ_cons] using hprev

theorem zero_connection_left_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) (hi : i.val = 0) : (states i).lo = r.lo := by
  have hhead := connectionBudget_zero_head (List.ofFn states) r.lo r.hi hzero
  have hM : 0 < M := by have := i.isLt; omega
  simp only [List.head?_eq_getElem?, List.getElem?_ofFn, dite_eq_left hM,
    Option.map_some, Option.getD_some] at hhead
  have hequal : (⟨0, hM⟩ : Fin M) = i := Fin.ext hi.symm
  rw [hequal] at hhead
  exact hhead

theorem zero_connection_right_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) :
    (states i).hi = connectionPrefixBoundary (List.ofFn states) r.hi (i.val + 1) := by
  have h := connectionBudget_zero_right (List.ofFn states) r.lo r.hi hzero i.val
    (by simp only [List.length_ofFn]; exact i.isLt)
  rw [List.getElem_ofFn] at h
  exact h

/-- Full endpoint distance, including first/last endpoints, for every two
members of the literal computed band. -/
theorem computedBand_child_endpoint_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child : Fin M → TargetInterval ny → ℚ)
    (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (i : Fin M) :
    (targetEndpointDistance (states i) (states' i) : ℝ) ≤ 4 * (theta : ℝ) * b / M := by
  have hthetaR : (0 : ℝ) ≤ theta := by exact_mod_cast htheta
  have hthetaBound : 0 ≤ 2 * (theta : ℝ) * b / M := by positivity
  obtain ⟨hnonempty, hwide, hv, hpredicate⟩ := computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hwide', hv', hpredicate'⟩ := computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  have hlo : (Nat.dist (states i).lo (states' i).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    by_cases hi : 0 < i.val
    · exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates' i hi
    · have hi0 : i.val = 0 := by omega
      rw [zero_connection_left_endpoint r states hpredicate.1 i hi0,
        zero_connection_left_endpoint r states' hpredicate'.1 i hi0, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  have hhi : (Nat.dist (states i).hi (states' i).hi : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    rw [zero_connection_right_endpoint r states hpredicate.1 i,
      zero_connection_right_endpoint r states' hpredicate'.1 i]
    by_cases hnext : i.val + 1 < M
    · rw [connectionPrefixBoundary_ofFn states r.hi ⟨i.val + 1, hnext⟩,
        connectionPrefixBoundary_ofFn states' r.hi ⟨i.val + 1, hnext⟩]
      exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates'
        ⟨i.val + 1, hnext⟩ (by change 0 < i.val + 1; omega)
    · have hdrop : M ≤ i.val + 1 := by omega
      simp only [connectionPrefixBoundary, List.drop_eq_nil_iff.mpr
        (show (List.ofFn states).length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.drop_eq_nil_iff.mpr
        (show (List.ofFn states').length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.head?_nil, Option.map_none, Option.getD_none, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  unfold targetEndpointDistance
  push_cast
  convert add_le_add hlo hhi using 1
  ring

/-- Grid soundness of the literal local box enumeration. -/
theorem gridStateBox_on_grid {n g radius lo hi : ℕ} (hg : 0 < g)
    (state : TargetInterval n) (hstate : state ∈ gridStateBox n g radius lo hi) :
    g ∣ state.lo ∧ g ∣ state.hi := by
  obtain ⟨s, hs, htail⟩ := List.mem_flatMap.mp hstate
  obtain ⟨t, htpoint, hmade⟩ := List.mem_filterMap.mp htail
  unfold makeTargetState at hmade
  split_ifs at hmade with hvalid
  · cases Option.some.inj hmade
    exact ⟨(gridPointsBetween_sound hg hs).2.2, (gridPointsBetween_sound hg htpoint).2.2⟩

theorem wideActionList_on_grid {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) :
    ∀ i, seedGridSpacing b P ∣ (action i).lo ∧ seedGridSpacing b P ∣ (action i).hi := by
  intro i
  exact gridStateBox_on_grid (by unfold seedGridSpacing; omega) (action i)
    (finiteAssignments_sound M _ action haction i)

end EditApproximation

end OAI

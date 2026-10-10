import OAI.Combinatorics.EditApproximation.Geometry.PrefixCosts
import OAI.Combinatorics.EditApproximation.Geometry.WideActions
import OAI.Combinatorics.EditApproximation.Geometry.SourcePrefixes

namespace OAI

/-!
# Actual comparison prefixes in the finite wide action family

The cut is the start of the remaining comparator suffix, or the parent's
end when that suffix is empty. Splitting at this cut preserves the literal
connection budget. Splicing any enumerated prefix to the comparator suffix
remains an enumerated wide action.
-/

namespace EditApproximation

open Finset

def connectionPrefixBoundary {n : ℕ} (states : List (TargetInterval n)) (finish j : ℕ) : ℕ :=
  ((states.drop j).head?.map TargetInterval.lo).getD finish

theorem realConnectionBudget_nonneg {n : ℕ} (start finish : ℝ)
    (states : List (TargetInterval n)) : 0 ≤ realConnectionBudget start states finish := by
  induction states generalizing start with
  | nil => exact abs_nonneg _
  | cons state rest ih => exact add_nonneg (abs_nonneg _) (ih state.hi)

/-- Exact splitting at the first endpoint of the remaining suffix. -/
theorem realConnectionBudget_split {n : ℕ} (states : List (TargetInterval n))
    (start : ℝ) (finish j : ℕ) :
    realConnectionBudget start states finish =
      realConnectionBudget start (states.take j) (connectionPrefixBoundary states finish j) +
      realConnectionBudget (connectionPrefixBoundary states finish j) (states.drop j) finish := by
  induction states generalizing start j with
  | nil => simp [connectionPrefixBoundary, realConnectionBudget]
  | cons state rest ih =>
    cases j with
    | zero => simp [connectionPrefixBoundary, realConnectionBudget]
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons, connectionPrefixBoundary,
        realConnectionBudget]
      rw [ih (state.hi : ℝ) j]
      dsimp only [connectionPrefixBoundary]
      ring

/-- A detour through an arbitrary real cut only increases the budget. -/
theorem realConnectionBudget_append_le {n : ℕ} (before after : List (TargetInterval n))
    (start finish cut : ℝ) :
    realConnectionBudget start (before ++ after) finish ≤
      realConnectionBudget start before cut + realConnectionBudget cut after finish := by
  induction before generalizing start with
  | nil =>
    cases after with
    | nil => exact abs_sub_le start cut finish
    | cons state rest =>
      have h := abs_sub_le start cut (state.lo : ℝ)
      simp only [List.nil_append, realConnectionBudget]
      linarith
  | cons state rest ih =>
    have h := ih (state.hi : ℝ)
    simp only [List.cons_append, realConnectionBudget]
    linarith

theorem zero_connection_prefix_suffix {n M : ℕ} (r : TargetInterval n)
    (comparison : Fin M → TargetInterval n) (j : ℕ)
    (hzero : endpointActionConnection r comparison = 0) :
    realConnectionBudget r.lo ((List.ofFn comparison).take j)
        (connectionPrefixBoundary (List.ofFn comparison) r.hi j) = 0 ∧
      realConnectionBudget (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
        ((List.ofFn comparison).drop j) r.hi = 0 := by
  have hsplit := realConnectionBudget_split (List.ofFn comparison) (r.lo : ℝ) r.hi j
  have hfull : realConnectionBudget r.lo (List.ofFn comparison) r.hi = 0 := by
    rw [realConnectionBudget_cast]
    exact_mod_cast hzero
  rw [hfull] at hsplit
  have hbefore := realConnectionBudget_nonneg (r.lo : ℝ)
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
    ((List.ofFn comparison).take j)
  have hafter := realConnectionBudget_nonneg
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j) (r.hi : ℝ)
    ((List.ofFn comparison).drop j)
  constructor <;> linarith

def comparisonPrefixSplice {n M : ℕ} (before comparison : Fin M → TargetInterval n)
    (j : ℕ) : Fin M → TargetInterval n := fun i => if i.val < j then before i else comparison i

theorem comparisonPrefixSplice_list {n M : ℕ} (before comparison : Fin M → TargetInterval n)
    (j : ℕ) (hj : j ≤ M) :
    List.ofFn (comparisonPrefixSplice before comparison j) =
      (List.ofFn before).take j ++ (List.ofFn comparison).drop j := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left hj]
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn, comparisonPrefixSplice]
    by_cases hij : i < j
    · rw [ite_eq_left hij, List.getElem_append_left]
      · rw [List.getElem_take, List.getElem_ofFn]
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj]
        exact hij
    · rw [ite_eq_right hij, List.getElem_append_right]
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj,
          List.getElem_drop, List.getElem_ofFn]
        congr 1
        apply Fin.ext
        change i = j + (i - j)
        omega
      · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hj]
        omega

theorem comparisonPrefixSplice_mem {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (before comparison : Fin M → TargetInterval ny) (j : ℕ)
    (hbefore : before ∈ wideActionList M parent r b P)
    (hcomparison : comparison ∈ wideActionList M parent r b P) :
    comparisonPrefixSplice before comparison j ∈ wideActionList M parent r b P := by
  apply finiteAssignments_complete
  intro i
  unfold comparisonPrefixSplice
  split_ifs with hi
  · exact finiteAssignments_sound M _ before hbefore i
  · exact finiteAssignments_sound M _ comparison hcomparison i

noncomputable def comparisonPrefixShift {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny) (j : ℕ) : ℝ :=
  (connectionPrefixBoundary (List.ofFn comparison) r.hi j : ℝ) -
    balancedCut parent.lo (parent.hi - parent.lo) M j

theorem connectionPrefixBoundary_ofFn {n M : ℕ} (states : Fin M → TargetInterval n)
    (finish : ℕ) (j : Fin M) :
    connectionPrefixBoundary (List.ofFn states) finish j.val = (states j).lo := by
  simp only [connectionPrefixBoundary, List.head?_drop, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.map_some, Option.getD_some]

/-- Internal comparison cuts are exactly the next child's left shift. -/
theorem comparisonPrefixShift_at_child {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny) (j : Fin M) :
    comparisonPrefixShift parent r comparison j.val =
      ((comparison j).lo : ℝ) - (sourceChild parent j).lo := by
  simp only [comparisonPrefixShift, connectionPrefixBoundary_ofFn, sourceChild]

noncomputable def comparisonPrefixValue {ny M : ℕ} (comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if i.val < j then child i (comparison i) else 0

theorem comparisonPrefixCost_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ)
    (hzero : endpointActionConnection r comparison = 0) :
    widePrefixCost parent r comparison child j (comparisonPrefixShift parent r comparison j) =
      comparisonPrefixValue comparison child j := by
  have hprefix := (zero_connection_prefix_suffix r comparison j hzero).1
  have hfinish : (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) +
      comparisonPrefixShift parent r comparison j =
      connectionPrefixBoundary (List.ofFn comparison) r.hi j := by
    unfold comparisonPrefixShift
    ring
  simp only [widePrefixCost, hfinish, hprefix, zero_add, comparisonPrefixValue]

/-- An arbitrary actual wide prefix can be completed by the comparator
suffix at exactly the comparison cut. -/
theorem comparisonPrefixSplice_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (before comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) :
    endpointActionValue r (comparisonPrefixSplice before comparison j) child ≤
      widePrefixCost parent r before child j (comparisonPrefixShift parent r comparison j) +
        (∑ i, child i (comparison i)) - comparisonPrefixValue comparison child j := by
  have hsuffix := (zero_connection_prefix_suffix r comparison j hzero).2
  have hconnection := realConnectionBudget_append_le
    ((List.ofFn before).take j) ((List.ofFn comparison).drop j) (r.lo : ℝ) (r.hi : ℝ)
    (connectionPrefixBoundary (List.ofFn comparison) r.hi j)
  rw [← comparisonPrefixSplice_list before comparison j hj,
    realConnectionBudget_cast, hsuffix, add_zero] at hconnection
  have hsum : (∑ i, child i (comparisonPrefixSplice before comparison j i)) =
      (∑ i, if i.val < j then child i (before i) else 0) +
        (∑ i, child i (comparison i)) - comparisonPrefixValue comparison child j := by
    unfold comparisonPrefixValue
    rw [← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp [comparisonPrefixSplice, hij]
  have hfinish : (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) +
      comparisonPrefixShift parent r comparison j =
      connectionPrefixBoundary (List.ofFn comparison) r.hi j := by
    unfold comparisonPrefixShift
    ring
  unfold endpointActionValue widePrefixCost
  rw [hfinish, hsum]
  change (connectionBudget r.lo (List.ofFn (comparisonPrefixSplice before comparison j)) r.hi : ℝ) + _ ≤ _
  linarith

/-- The comparison prefix is covered by the literal finite predictor.
The full-action lower bound is later instantiated by the actual warmup
Bellman value; no prefix estimate is assumed. -/
theorem comparisonPrefixMinimum_bounds {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) (fullLower : ℝ)
    (hfull : ∀ action ∈ wideActionList M parent r b P,
      fullLower ≤ endpointActionValue r action child) :
    comparisonPrefixValue comparison child j - ((∑ i, child i (comparison i)) - fullLower) ≤
        widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j) ∧
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
          (comparisonPrefixShift parent r comparison j) ≤ comparisonPrefixValue comparison child j := by
  constructor
  · apply le_widePrefixMinimum
    intro action ha
    have hsplice := comparisonPrefixSplice_mem parent r action comparison j ha hcomparison
    have hcost := comparisonPrefixSplice_cost parent r action comparison child j hj hzero
    have hlower := hfull _ hsplice
    linarith
  · exact (widePrefixMinimum_le_member parent r _ hnonempty child j _ comparison hcomparison).trans_eq
      (comparisonPrefixCost_eq parent r comparison child j hzero)

/-- Real form of the literal local wide-action minimum; the first member
is duplicated as fallback, exactly as in the rational predictor. -/
noncomputable def wideActionMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) : ℝ :=
  finiteMinimum (endpointActionValue r ((wideActionList M parent r b P).head hnonempty) child)
    ((wideActionList M parent r b P).map fun action => endpointActionValue r action child)

theorem wideActionMinimum_le_member {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) :
    wideActionMinimum parent r b P hnonempty child ≤ endpointActionValue r action child :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

/-- Exact finite predictor coverage with its actual wide-action minimum Z. -/
theorem comparisonPrefixMinimum_actual_bounds {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (hj : j ≤ M)
    (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixValue comparison child j -
        ((∑ i, child i (comparison i)) - wideActionMinimum parent r b P hnonempty child) ≤
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
        (comparisonPrefixShift parent r comparison j) ∧
      widePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j
        (comparisonPrefixShift parent r comparison j) ≤ comparisonPrefixValue comparison child j :=
  comparisonPrefixMinimum_bounds parent r comparison hcomparison hnonempty child j hj hzero
    (wideActionMinimum parent r b P hnonempty child)
    (fun action ha => wideActionMinimum_le_member parent r hnonempty child action ha)

/-- A zero connection path has exactly the endpoint length span. -/
theorem connectionBudget_zero_span {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0) :
    start ≤ finish ∧ (states.map fun state => state.hi - state.lo).sum = finish - start := by
  induction states generalizing start with
  | nil =>
    have heq : start = finish := Nat.eq_of_dist_eq_zero hzero
    subst start
    simp only [List.map_nil, List.sum_nil, Nat.sub_self, le_refl, and_self]
  | cons state rest ih =>
    have hparts : Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 := hzero
    have hstart : start = state.lo := Nat.eq_of_dist_eq_zero (by omega)
    have htail : connectionBudget state.hi rest finish = 0 := by omega
    obtain ⟨horder, hsum⟩ := ih state.hi htail
    subst start
    constructor
    · exact state.ordered.trans horder
    · simp only [List.map_cons, List.sum_cons, hsum]
      have := state.ordered
      omega

/-- The comparison cut displacement is the sum of the actual target-minus-
source child length gaps in its prefix. -/
theorem comparisonPrefixShift_gap_sum {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (r : TargetInterval target.length) (comparison : Fin M → TargetInterval target.length)
    (j : ℕ) (hj : j ≤ M) (hzero : endpointActionConnection r comparison = 0) :
    comparisonPrefixShift parent r comparison j - comparisonPrefixShift parent r comparison 0 =
      ∑ i, if i.val < j then
        stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
          target (comparison i) else 0 := by
  let cut := connectionPrefixBoundary (List.ofFn comparison) r.hi j
  have hprefix := (zero_connection_prefix_suffix r comparison j hzero).1
  have hprefixNat : connectionBudget r.lo ((List.ofFn comparison).take j) cut = 0 := by
    rw [realConnectionBudget_cast] at hprefix
    exact_mod_cast hprefix
  obtain ⟨htargetOrder, htargetSpan⟩ := connectionBudget_zero_span
    ((List.ofFn comparison).take j) r.lo cut hprefixNat
  have htargetNat : (∑ i : Fin M with i.val < j, ((comparison i).hi - (comparison i).lo)) = cut - r.lo := by
    rw [← List.sum_take_ofFn]
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using htargetSpan
  have hsourceSpan := sourceChildren_prefix_length source hM parent j hj
  simp only [List.length_flatten, List.map_take, List.map_ofFn, Function.comp_def] at hsourceSpan
  have hsourceNat : (∑ i : Fin M with i.val < j,
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length) =
        balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo := by
    rw [← List.sum_take_ofFn]
    exact hsourceSpan
  have htargetReal : (∑ i : Fin M, if i.val < j then
      ((comparison i).hi : ℝ) - (comparison i).lo else 0) = (cut : ℝ) - r.lo := by
    rw [← sum_filter]
    calc
      _ = ((∑ i : Fin M with i.val < j, ((comparison i).hi - (comparison i).lo) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        apply sum_congr rfl
        intro i hi
        rw [Nat.cast_sub (comparison i).ordered]
      _ = ((cut - r.lo : ℕ) : ℝ) := congrArg (fun a : ℕ => (a : ℝ)) htargetNat
      _ = _ := Nat.cast_sub htargetOrder
  have hsourceOrder := (balancedCut_bounds parent.lo (parent.hi - parent.lo) M j hM hj).1
  have hsourceReal : (∑ i : Fin M, if i.val < j then
      ((substring source (sourceChild parent i).lo (sourceChild parent i).hi).length : ℝ) else 0) =
        (balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) - parent.lo := by
    rw [← sum_filter]
    calc
      _ = ((∑ i : Fin M with i.val < j,
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
      _ = ((balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo : ℕ) : ℝ) := congrArg (fun a : ℕ => (a : ℝ)) hsourceNat
      _ = _ := Nat.cast_sub hsourceOrder
  have hgap : (∑ i : Fin M, if i.val < j then
      stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        target (comparison i) else 0) =
      (cut : ℝ) - r.lo - ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) - parent.lo) := by
    rw [← htargetReal, ← hsourceReal, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hij : i.val < j <;> simp only [hij, ↓reduceIte, stateLengthGap, sub_zero]
  have horigin := (zero_connection_prefix_suffix r comparison 0 hzero).1
  simp only [List.take_zero, realConnectionBudget] at horigin
  have horiginEq : (connectionPrefixBoundary (List.ofFn comparison) r.hi 0 : ℝ) = r.lo := by
    exact (sub_eq_zero.mp (abs_eq_zero.mp horigin)).symm
  rw [hgap]
  unfold comparisonPrefixShift
  rw [balancedCut_zero, horiginEq]
  dsimp only [cut]
  ring

end EditApproximation

end OAI

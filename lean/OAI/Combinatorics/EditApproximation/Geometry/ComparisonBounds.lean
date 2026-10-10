import OAI.Combinatorics.EditApproximation.Geometry.ComparisonTree

namespace OAI

/-! Actual terminal, nonterminal-cost and endpoint-movement bounds. -/

namespace EditApproximation

open Finset

noncomputable def comparisonActiveCost {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun node => match node with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0
      else stateEditCost (substring source parent.lo parent.hi) target q

noncomputable def comparisonMovement {α : Type*} (source target : List α) (P : ℕ) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun node => match node with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0 else
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q)

theorem comparisonActiveCost_bounds {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonActiveCost source target node ∧
      comparisonActiveCost source target node ≤ comparisonStateCost source target node := by
  classical
  cases node with
  | none => exact ⟨le_rfl, le_rfl⟩
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonActiveCost, ite_eq_left hs, comparisonStateCost]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
    · simp only [comparisonActiveCost, ite_eq_right hs, comparisonStateCost]
      exact ⟨Nat.cast_nonneg _, le_rfl⟩

theorem comparisonMovement_bound {α : Type*} (source target : List α)
    (P : ℕ) (hP : 0 < P) (node : ComparisonState source.length target.length) :
    comparisonMovement source target P node * P ≤ 2 * comparisonActiveCost source target node := by
  classical
  cases node with
  | none => simp only [comparisonMovement, comparisonActiveCost, zero_mul, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonMovement, comparisonActiveCost, ite_eq_left hs, zero_mul, mul_zero, le_refl]
    · have hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hs
        omega
      have hb := (cost_dyadicScale _ _ hc le_rfl).2.1
      have herror := rounded_seedGrid_error
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP q
      have herrorR : (targetEndpointDistance q (roundInterval (seedGridSpacing
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q) : ℝ) * P ≤
          2 * (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ) := by
        exact_mod_cast herror
      have hbR : ((2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ) : ℝ) ≤
          stateEditCost (substring source parent.lo parent.hi) target q := by exact_mod_cast hb
      simp only [comparisonMovement, comparisonActiveCost, ite_eq_right hs]
      linarith

theorem comparison_total_active_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d, comparisonActiveCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * J * comparisonStateCost source target root := by
  have hlevel (d : ℕ) (hd : d ∈ range J) :
      (∑ node : TreeLayer M d, comparisonActiveCost source target
        (comparisonFrontier source target hM P hP root d node)) ≤
          2 * comparisonStateCost source target root := by
    exact (sum_le_sum (fun node _ => (comparisonActiveCost_bounds source target _).2)).trans
      (comparison_frontier_cost_le_twice source target hM P hP root J d (mem_range.mp hd).le hsmall)
  have hsum := sum_le_sum hlevel
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_left_comm] using hsum

theorem comparison_total_movement_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d, comparisonMovement source target P
      (comparisonFrontier source target hM P hP root d node)) ≤
        4 * J * comparisonStateCost source target root / P := by
  have hPpos : 0 < P := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hsum := sum_le_sum (fun d (_ : d ∈ range J) => sum_le_sum
    (fun node (_ : node ∈ (univ : Finset (TreeLayer M d))) =>
      comparisonMovement_bound source target P hPpos
        (comparisonFrontier source target hM P hP root d node)))
  simp only [← sum_mul, ← mul_sum] at hsum
  have hcost := comparison_total_active_cost_bound source target hM P hP root J hsmall
  apply (le_div_iff₀ hPr).2
  linarith

theorem comparisonStep_stopped_or_width {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) (w : ℕ)
    (hnode : ∀ parent q, node = some (parent, q) →
      comparisonStopped source target parent q ∨ parent.hi - parent.lo ≤ w)
    (i : Fin M) (resultParent : TargetInterval source.length) (resultQ : TargetInterval target.length)
    (heq : comparisonStep source target hM P hP node i = some (resultParent, resultQ)) :
    comparisonStopped source target resultParent resultQ ∨
      resultParent.hi - resultParent.lo ≤ w ⌈/⌉ M := by
  classical
  cases node with
  | none => cases heq
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs] at heq
      split_ifs at heq with hi
      have hpq := Option.some.inj heq
      have hp : parent = resultParent := congrArg Prod.fst hpq
      have hq : q = resultQ := congrArg Prod.snd hpq
      exact Or.inl (by rw [← hp, ← hq]; exact hs)
    · simp only [comparisonStep, dite_eq_right hs] at heq
      have hpq := Option.some.inj heq
      have hp : sourceChild parent i = resultParent := congrArg Prod.fst hpq
      have hw := (hnode parent q rfl).resolve_left hs
      apply Or.inr
      rw [← hp]
      exact (sourceChild_width_le_ceiling parent i).trans ((gc_mul_ceilDiv hM).monotone_l hw)

theorem comparison_frontier_stopped_or_width {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (rootParent : TargetInterval source.length) (rootQ : TargetInterval target.length)
    (d : ℕ) (node : TreeLayer M d)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP (some (rootParent, rootQ)) d node = some (parent, q)) :
    comparisonStopped source target parent q ∨
      parent.hi - parent.lo ≤ (rootParent.hi - rootParent.lo) ⌈/⌉ M ^ d := by
  induction d generalizing parent q with
  | zero =>
    change some (rootParent, rootQ) = some (parent, q) at heq
    have hp : rootParent = parent := congrArg Prod.fst (Option.some.inj heq)
    apply Or.inr
    rw [← hp, pow_zero]
    simp
  | succ d ih =>
    have h := comparisonStep_stopped_or_width source target hM P hP
      (comparisonFrontier source target hM P hP (some (rootParent, rootQ)) d node.1)
      ((rootParent.hi - rootParent.lo) ⌈/⌉ M ^ d)
      (fun parent q heq => ih node.1 parent q heq) node.2 parent q heq
    rw [ceilDiv_comp _ _ _ (pow_pos hM d) hM, ← pow_succ] at h
    exact h

theorem comparison_frontier_terminal {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (rootParent : TargetInterval source.length) (rootQ : TargetInterval target.length) (J : ℕ)
    (hcapacity : rootParent.hi - rootParent.lo ≤ M ^ J) (node : TreeLayer M J)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP (some (rootParent, rootQ)) J node = some (parent, q)) :
    comparisonStopped source target parent q := by
  rcases comparison_frontier_stopped_or_width source target hM P hP rootParent rootQ J node parent q heq with h | h
  · exact h
  · apply Or.inl
    exact h.trans ((ceilDiv_le_iff_le_mul (pow_pos hM J)).2 (by simpa using hcapacity))

theorem comparison_frontier_cost_slack {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ node : TreeLayer M J, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root J node)) ≤
        (1 + 8 * (M : ℝ) * J / P) * comparisonStateCost source target root := by
  have hx : 0 ≤ 4 * (M : ℝ) / P := by positivity
  have hpow := small_growth_pow J hx hsmall
  have heq : 1 + 2 * (J : ℝ) * (4 * (M : ℝ) / P) = 1 + 8 * (M : ℝ) * J / P := by ring
  rw [heq] at hpow
  exact (comparison_frontier_cost_bound source target hM P hP root J).trans
    (mul_le_mul_of_nonneg_right hpow (comparisonStateCost_nonneg source target root))

end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Geometry.RoundedComparison
import OAI.Combinatorics.EditApproximation.Geometry.BalancedWidths

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

abbrev ComparisonState (nx ny : ℕ) := Option (TargetInterval nx × TargetInterval ny)

noncomputable def comparisonStateCost {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ
  | none => 0
  | some (parent, q) => stateEditCost (substring source parent.lo parent.hi) target q

def comparisonStopped {α : Type*} (source target : List α)
    (parent : TargetInterval source.length) (q : TargetInterval target.length) : Prop :=
  parent.hi - parent.lo ≤ 1 ∨ stateEditCost (substring source parent.lo parent.hi) target q = 0

noncomputable def comparisonChildren {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    Fin M → TargetInterval target.length :=
  Classical.choose (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)

theorem comparisonChildren_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
      target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) ≤
        (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  (Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)).2.2.2.2

theorem comparisonChildren_spec {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
    let r := roundInterval (seedGridSpacing b P) q
    let states := comparisonChildren source target hM P hP parent q hc
    states ∈ wideActionList M parent r b P ∧ endpointActionConnection r states = 0 ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      (∀ i : Fin M,
        Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
        Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b) ∧
      (∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ)) ≤
          (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)

theorem comparisonChildren_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
    let r := roundInterval (seedGridSpacing b P) q
    (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) +
          targetEndpointDistance q r := by
  dsimp only
  let r := roundInterval (seedGridSpacing
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
  have hlower := zero_connection_cost_sum_lower source target hM parent r
    (comparisonChildren source target hM P hP parent q hc)
    (comparisonChildren_spec source target hM P hP parent q hc).2.1
  have hspatial : (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      stateEditCost (substring source parent.lo parent.hi) target r + targetEndpointDistance q r := by
    exact_mod_cast stateEditCost_spatial (substring source parent.lo parent.hi) target q r
  linarith

noncomputable def comparisonStep {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) :
    ComparisonState source.length target.length → Fin M → ComparisonState source.length target.length
    := by
  classical
  exact fun node i => match node with
    | none => none
    | some (parent, q) =>
      if hstop : comparisonStopped source target parent q then
        if i = ⟨0, hM⟩ then some (parent, q) else none
      else
        some (sourceChild parent i,
          comparisonChildren source target hM P hP parent q
            (by unfold comparisonStopped at hstop; omega) i)

theorem comparisonStateCost_nonneg {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonStateCost source target node := by
  cases node with
  | none => exact le_rfl
  | some state => exact Nat.cast_nonneg _

theorem comparisonStep_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) :
    (∑ i, comparisonStateCost source target (comparisonStep source target hM P hP node i)) ≤
      (1 + 4 * (M : ℝ) / P) * comparisonStateCost source target node := by
  classical
  cases node with
  | none => simp only [comparisonStep, comparisonStateCost, sum_const_zero, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs]
      have hsum : (∑ i : Fin M, comparisonStateCost source target
          (if i = ⟨0, hM⟩ then some (parent, q) else none)) =
          comparisonStateCost source target (some (parent, q)) := by
        have hpoint (i : Fin M) : comparisonStateCost source target
            (if i = ⟨0, hM⟩ then some (parent, q) else none) =
            if i = ⟨0, hM⟩ then comparisonStateCost source target (some (parent, q)) else 0 := by
          split_ifs <;> rfl
        simp_rw [hpoint]
        simp
      rw [hsum]
      have hnonneg := comparisonStateCost_nonneg source target (some (parent, q))
      have hf : 0 ≤ 4 * (M : ℝ) / P := by positivity
      nlinarith
    · simpa only [comparisonStep, dite_eq_right hs, comparisonStateCost] using
        comparisonChildren_cost_bound source target hM P hP parent q
          (by unfold comparisonStopped at hs; omega)

noncomputable def comparisonFrontier {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) :
    (d : ℕ) → TreeLayer M d → ComparisonState source.length target.length
  | 0, _ => root
  | d + 1, node => comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP root d node.1) node.2

theorem comparison_frontier_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (d : ℕ) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        (1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root := by
  induction d with
  | zero =>
    change (∑ _ : PUnit, comparisonStateCost source target root) ≤ _
    simp
  | succ d ih =>
    rw [← tree_layer_sum]
    have hsum := sum_le_sum (fun node (_ : node ∈ (univ : Finset (TreeLayer M d))) =>
      comparisonStep_cost_bound source target hM P hP
        (comparisonFrontier source target hM P hP root d node))
    have hf : 0 ≤ 1 + 4 * (M : ℝ) / P := by positivity
    calc
      _ ≤ ∑ node : TreeLayer M d, (1 + 4 * (M : ℝ) / P) *
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := hsum
      _ = (1 + 4 * (M : ℝ) / P) * ∑ node : TreeLayer M d,
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := by rw [mul_sum]
      _ ≤ (1 + 4 * (M : ℝ) / P) *
          ((1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root) :=
            mul_le_mul_of_nonneg_left ih hf
      _ = _ := by rw [pow_succ]; ring

theorem comparison_frontier_cost_le_twice {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J d : ℕ) (hd : d ≤ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * comparisonStateCost source target root := by
  have hx : 0 ≤ 4 * (M : ℝ) / P := by positivity
  have hdR : (d : ℝ) ≤ J := by exact_mod_cast hd
  have hdx : (d : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hdR hx).trans hsmall
  have hpow := small_growth_pow d hx hdx
  have htwo : (1 + 4 * (M : ℝ) / P) ^ d ≤ 2 := by linarith
  exact (comparison_frontier_cost_bound source target hM P hP root d).trans
    (mul_le_mul_of_nonneg_right htwo (comparisonStateCost_nonneg source target root))

end EditApproximation

end OAI

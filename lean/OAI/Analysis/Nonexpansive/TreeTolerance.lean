import OAI.Analysis.Nonexpansive.OrderedTree
import OAI.Analysis.Nonexpansive.SwitchingScalar

namespace OAI

/-!
# Tolerances from the actual budgets on the tree

At every positive depth, take the minimum of all budgets at that level and
all earlier positive levels, capped by one.  The cap makes the construction
work for arbitrary positive budgets.  When those budgets are at most one,
the cumulative minimum at every positive depth is attained by an actual
node, so the cap does not change the prescribed finite minimum.

The tolerance is the cumulative minimum multiplied by the dyadic coefficient
`2^(-(k+1))`.  Its value at depth zero is exactly one half.  Every finite tail
is bounded by every actual budget at its initial or an earlier depth.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace OrderedTree

noncomputable section

variable (T : OrderedTree) (e : (Σ k, T.Node (k + 1)) → ℝ)

/-- Every positive level has at least one actual node. -/
theorem budgetLevel_nonempty (k : ℕ) :
    (Finset.univ : Finset (T.Node (k + 1))).Nonempty :=
  ⟨⟨0, T.size_pos (k + 1)⟩, Finset.mem_univ _⟩

/-- The minimum of all actual budgets at positive depth `k+1`. -/
def levelMinimum (k : ℕ) : ℝ :=
  Finset.univ.inf' (T.budgetLevel_nonempty k) (fun v => e ⟨k, v⟩)

theorem levelMinimum_le (k : ℕ) (v : T.Node (k + 1)) :
    T.levelMinimum e k ≤ e ⟨k, v⟩ := by
  exact Finset.inf'_le (fun v => e ⟨k, v⟩) (Finset.mem_univ v)

theorem le_levelMinimum_iff (k : ℕ) (a : ℝ) :
    a ≤ T.levelMinimum e k ↔ ∀ v : T.Node (k + 1), a ≤ e ⟨k, v⟩ := by
  simp only [levelMinimum, Finset.le_inf'_iff, Finset.mem_univ, forall_true_left]

theorem levelMinimum_pos (he : ∀ v, 0 < e v) (k : ℕ) :
    0 < T.levelMinimum e k := by
  apply (Finset.lt_inf'_iff (T.budgetLevel_nonempty k)).2
  intro v _
  exact he ⟨k, v⟩

theorem levelMinimum_attained (k : ℕ) :
    ∃ v : T.Node (k + 1), T.levelMinimum e k = e ⟨k, v⟩ := by
  obtain ⟨v, _, hv⟩ :=
    Finset.exists_mem_eq_inf' (T.budgetLevel_nonempty k) (fun v => e ⟨k, v⟩)
  exact ⟨v, hv⟩

/-- The actual cumulative minimum, with the initial cap equal to one. -/
def cumulativeMinimum : ℕ → ℝ
  | 0 => 1
  | k + 1 => min (cumulativeMinimum k) (T.levelMinimum e k)

@[simp] theorem cumulativeMinimum_zero : T.cumulativeMinimum e 0 = 1 := rfl

@[simp] theorem cumulativeMinimum_succ (k : ℕ) :
    T.cumulativeMinimum e (k + 1) =
      min (T.cumulativeMinimum e k) (T.levelMinimum e k) := rfl

theorem cumulativeMinimum_pos (he : ∀ v, 0 < e v) (k : ℕ) :
    0 < T.cumulativeMinimum e k := by
  induction k with
  | zero => norm_num [cumulativeMinimum]
  | succ k ih =>
      exact lt_min ih (T.levelMinimum_pos e he k)

theorem cumulativeMinimum_antitone : Antitone (T.cumulativeMinimum e) := by
  apply antitone_nat_of_succ_le
  intro k
  exact min_le_left _ _

theorem cumulativeMinimum_le_one (k : ℕ) : T.cumulativeMinimum e k ≤ 1 :=
  T.cumulativeMinimum_antitone e (Nat.zero_le k)

theorem cumulativeMinimum_le_budget {i k : ℕ} (hik : i + 1 ≤ k)
    (v : T.Node (i + 1)) : T.cumulativeMinimum e k ≤ e ⟨i, v⟩ := by
  calc
    T.cumulativeMinimum e k ≤ T.cumulativeMinimum e (i + 1) :=
      T.cumulativeMinimum_antitone e hik
    _ ≤ T.levelMinimum e i := min_le_right _ _
    _ ≤ e ⟨i, v⟩ := T.levelMinimum_le e i v

/-- Exact lower-bound characterization of the finite minimum: it includes
every budget through depth `k`, without choosing a branch of the tree. -/
theorem le_cumulativeMinimum_iff (k : ℕ) (a : ℝ) :
    a ≤ T.cumulativeMinimum e k ↔
      a ≤ 1 ∧ ∀ i < k, ∀ v : T.Node (i + 1), a ≤ e ⟨i, v⟩ := by
  induction k with
  | zero => simp [cumulativeMinimum]
  | succ k ih =>
      rw [cumulativeMinimum_succ, le_min_iff, ih, le_levelMinimum_iff]
      constructor
      · rintro ⟨⟨ha, hprev⟩, hlast⟩
        refine ⟨ha, ?_⟩
        intro i hi v
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hik | rfl
        · exact hprev i hik v
        · exact hlast v
      · rintro ⟨ha, hlevels⟩
        refine ⟨⟨ha, ?_⟩, ?_⟩
        · intro i hi v
          exact hlevels i (Nat.lt_trans hi (Nat.lt_succ_self k)) v
        · exact hlevels k (Nat.lt_succ_self k)

/-- When actual budgets are at most one, the positive-depth minimum is
attained by an actual node.  Together with `cumulativeMinimum_le_budget`,
this identifies it with the uncapped minimum of the finite collection. -/
theorem cumulativeMinimum_attained (he : ∀ v, e v ≤ 1) (k : ℕ) :
    ∃ i < k + 1, ∃ v : T.Node (i + 1),
      T.cumulativeMinimum e (k + 1) = e ⟨i, v⟩ := by
  induction k with
  | zero =>
      obtain ⟨v, hv⟩ := T.levelMinimum_attained e 0
      refine ⟨0, Nat.lt_succ_self 0, v, ?_⟩
      rw [cumulativeMinimum_succ, cumulativeMinimum_zero, hv, min_eq_right (he ⟨0, v⟩)]
  | succ k ih =>
      rcases le_total (T.cumulativeMinimum e (k + 1)) (T.levelMinimum e (k + 1))
        with h | h
      · obtain ⟨i, hi, v, hv⟩ := ih
        refine ⟨i, Nat.lt_trans hi (Nat.lt_succ_self (k + 1)), v, ?_⟩
        rw [cumulativeMinimum_succ, min_eq_left h, hv]
      · obtain ⟨v, hv⟩ := T.levelMinimum_attained e (k + 1)
        refine ⟨k + 1, Nat.lt_succ_self (k + 1), v, ?_⟩
        rw [cumulativeMinimum_succ, min_eq_right h, hv]

/-- The dyadic tolerance obtained from the actual cumulative budgets. -/
def tolerance (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1) * T.cumulativeMinimum e k

@[simp] theorem tolerance_zero : T.tolerance e 0 = 1 / 2 := by
  simp [tolerance]

theorem tolerance_pos (he : ∀ v, 0 < e v) (k : ℕ) : 0 < T.tolerance e k :=
  mul_pos (pow_pos (by norm_num) _) (T.cumulativeMinimum_pos e he k)

theorem tolerance_le_dyadic (k : ℕ) :
    T.tolerance e k ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  simpa only [tolerance, mul_one] using
    mul_le_mul_of_nonneg_left (T.cumulativeMinimum_le_one e k)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1))

theorem tolerance_le_one (k : ℕ) : T.tolerance e k ≤ 1 :=
  (T.tolerance_le_dyadic e k).trans
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))

/-- The stronger dyadic finite-tail estimate.  The empty tail is included. -/
theorem tolerance_tail_le_dyadic (he : ∀ v, 0 < e v)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, T.tolerance e d) ≤
      (1 / 2 : ℝ) ^ k * T.cumulativeMinimum e k := by
  exact dyadic_weighted_tail_le (T.cumulativeMinimum e)
    (fun d => (T.cumulativeMinimum_pos e he d).le)
    (T.cumulativeMinimum_antitone e) k N hkN

/-- A tail starting at depth `k` is bounded by the dyadic coefficient times
the budget of any actual node at positive depth at most `k`. -/
theorem tolerance_tail_le_dyadic_budget (he : ∀ v, 0 < e v)
    {i k N : ℕ} (hik : i + 1 ≤ k) (hkN : k ≤ N) (v : T.Node (i + 1)) :
    (∑ d ∈ Finset.Ico k N, T.tolerance e d) ≤ (1 / 2 : ℝ) ^ k * e ⟨i, v⟩ := by
  exact (T.tolerance_tail_le_dyadic e he k N hkN).trans
    (mul_le_mul_of_nonneg_left (T.cumulativeMinimum_le_budget e hik v)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k))

/-- The unweighted node-budget bound used by the switching construction. -/
theorem tolerance_tail_le_budget (he : ∀ v, 0 < e v)
    {i k N : ℕ} (hik : i + 1 ≤ k) (hkN : k ≤ N) (v : T.Node (i + 1)) :
    (∑ d ∈ Finset.Ico k N, T.tolerance e d) ≤ e ⟨i, v⟩ := by
  exact dyadic_weighted_tail_le_budget (T.cumulativeMinimum e)
    (fun d => (T.cumulativeMinimum_pos e he d).le)
    (T.cumulativeMinimum_antitone e) k N hkN
    (T.cumulativeMinimum_le_budget e hik v)

end
end OrderedTree
end ReflexiveFixedPoints

end OAI

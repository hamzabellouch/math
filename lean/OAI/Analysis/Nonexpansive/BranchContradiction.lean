import OAI.Analysis.Nonexpansive.DenseDifferences
import OAI.Analysis.Nonexpansive.FeasibleBranch
import OAI.Analysis.Nonexpansive.FunctionalVanishing
import OAI.Analysis.Nonexpansive.WeakBranchIntersection
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The branch contradiction from the actual finite witnesses

The actual ordered tree supplies detector labels and summable budgets. The
finite switching witnesses give a feasible branch. Weak compactness of the
whole difference ball keeps one common vector, whereas the same detectors
vanish on its closed difference span by density and their uniform norm bound.
-/

open Filter Topology

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Two detector values in the same interval of length e differ by at most e. -/
theorem abs_apply_sub_le_of_detector (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (y a b : X) (e : ℝ)
    (hya : ‖y - a‖ ≤ 1) (hyb : ‖y - b‖ ≤ 1)
    (ha : 1 - e ≤ f (y - a)) (hb : 1 - e ≤ f (y - b)) :
    |f (a - b)| ≤ e := by
  have hupper (z : X) (hz : ‖y - z‖ ≤ 1) : f (y - z) ≤ 1 := by
    calc
      f (y - z) ≤ |f (y - z)| := le_abs_self _
      _ = ‖f (y - z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖y - z‖ := f.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul hf hz (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hua := hupper a hya
  have hub := hupper b hyb
  simp only [map_sub] at ha hb hua hub ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The precise outputs of the tree and finite switching construction cannot
coexist in the normalized minimal data. Every listed input is supplied by an
earlier concrete producer; no branch or pointwise-vanishing premise is used. -/
theorem tree_finite_witnesses_contradiction
    (D : NormalizedMinimalData (X := X)) (T : OrderedTree)
    (f : (k : ℕ) → T.Node k → (X →L[ℝ] ℝ))
    (y : (k : ℕ) → T.Node k → D.K)
    (e : (k : ℕ) → T.Node k → ℝ)
    (hnorm : ∀ k, 0 < k → ∀ v : T.Node k, ‖f k v‖ ≤ 1)
    (hdetector : ∀ k, 0 < k → ∀ v : T.Node k, ∀ i, i < k →
      1 - e k v ≤ f k v ((y k v : X) - (D.z i : X)))
    (hbudget : Summable (fun v : Σ k, T.Node (k + 1) => e (v.1 + 1) v.2))
    (hfinite : ∀ n, 0 < n → ∃ v : T.Node n,
      ∃ d ∈ differenceBall D.K,
        T.DetectsPrefix (fun k v x => f k v x) v d) :
    False := by
  have hB : (differenceBall D.K).Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ differenceSpan D.K ∧ ‖(0 : X)‖ ≤ 1
    exact ⟨(differenceSpan D.K).zero_mem, by simp⟩
  obtain ⟨b, _hbranch, hprefix⟩ :=
    T.exists_branch_of_finite_witnesses (differenceBall D.K)
      (fun k v x => f k v x) hB hfinite
  let φ : ℕ → X →L[ℝ] ℝ := fun n => f (n + 1) (b (n + 1))
  have hφ (n : ℕ) : ‖φ n‖ ≤ 1 := hnorm (n + 1) (Nat.succ_pos n) _
  have hprefixφ : ∀ n : ℕ, ∃ d ∈ differenceBall D.K,
      ∀ i < n, (1 / 2 : ℝ) ≤ φ i d := by
    intro n
    obtain ⟨d, hdB, hd⟩ := hprefix n
    refine ⟨d, hdB, ?_⟩
    intro i hi
    exact hd (i + 1) (Nat.succ_pos i) (Nat.succ_le_of_lt hi)
  obtain ⟨d, hdB, hlarge⟩ := exists_weaklyCompact_all_halfspaces
    (differenceBall D.K) D.weak_ball_compact φ (1 / 2) hprefixφ
  let branchIndex : ℕ → Σ k, T.Node (k + 1) := fun n => ⟨n, b (n + 1)⟩
  have hbranchIndex : Function.Injective branchIndex := by
    intro i j hij
    exact congrArg (fun v : Σ k, T.Node (k + 1) => v.1) hij
  have hezero : Tendsto (fun n => e (n + 1) (b (n + 1))) atTop (𝓝 0) :=
    summable_budget_tendsto
      (fun v : Σ k, T.Node (k + 1) => e (v.1 + 1) v.2)
      hbudget branchIndex hbranchIndex
  have hpair (i j : ℕ) :
      Tendsto (fun n => φ n ((D.z i : X) - (D.z j : X))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => e (n + 1) (b (n + 1))) _ hezero
    refine Filter.eventually_atTop.mpr ⟨max i j, ?_⟩
    intro n hn
    have hi : i < n + 1 := Nat.lt_succ_of_le ((le_max_left i j).trans hn)
    have hj : j < n + 1 := Nat.lt_succ_of_le ((le_max_right i j).trans hn)
    have h := abs_apply_sub_le_of_detector (φ n) (hφ n)
      (y (n + 1) (b (n + 1))) (D.z i) (D.z j) (e (n + 1) (b (n + 1)))
      (D.norm_sub_le_one _ _) (D.norm_sub_le_one _ _)
      (hdetector (n + 1) (Nat.succ_pos n) _ i hi)
      (hdetector (n + 1) (Nat.succ_pos n) _ j hj)
    simpa only [Real.norm_eq_abs] using h
  have hzero : Tendsto (fun n => φ n d) atTop (𝓝 0) := by
    apply tendsto_zero_of_mem_closedSpan φ hφ
      (s := Set.range (fun ij : ℕ × ℕ => (D.z ij.1 : X) - (D.z ij.2 : X)))
    · rintro x ⟨⟨i, j⟩, rfl⟩
      exact hpair i j
    · rw [closure_span_pairwiseDifferences_eq_differenceSpan D.z D.dense_z]
      exact hdB.1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hzero (1 / 4) (by linarith)
  have hsmall : |φ N d| < 1 / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hN N le_rfl
  have hlargeN := hlarge N
  have habs := le_abs_self (φ N d)
  linarith

end ReflexiveFixedPoints

end OAI

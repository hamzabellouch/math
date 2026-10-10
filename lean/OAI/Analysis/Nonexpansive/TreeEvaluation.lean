import OAI.Analysis.Nonexpansive.WeightedTree
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-!
# Actual nonlinear evaluation on a weighted ordered tree

The maps act on the literal subtype of a convex subset of a real normed
space. A cutoff value is an output: its own node map is not applied again.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

structure TreeEvaluation {T : OrderedTree} (W : WeightedTree T) (K : Set X) where
  convex : Convex ℝ K
  map : (k : ℕ) → T.Node k → K → K
  nonexpansive : ∀ k v, LipschitzWith 1 (map k v)

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- The actual convex average of the child outputs. -/
noncomputable def childAverage (k : ℕ) (H : T.Node (k + 1) → K)
    (p : T.Node k) : K := by
  classical
  refine ⟨∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
    W.weight k c • (H c : X), ?_⟩
  exact E.convex.sum_mem
    (fun c _ => le_of_lt (W.weight_pos k c))
    (W.weight_sum k p) (fun c _ => (H c).property)

@[simp] theorem childAverage_val (k : ℕ) (H : T.Node (k + 1) → K)
    (p : T.Node k) :
    (E.childAverage k H p : X) =
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c • (H c : X) := rfl

/-- One genuine level of the nonlinear recursive evaluation. -/
noncomputable def collapse (k : ℕ) (H : T.Node (k + 1) → K)
    (p : T.Node k) : K := E.map k p (E.childAverage k H p)

/-- Evaluate a cutoff assignment, applying maps strictly above its level. -/
noncomputable def evaluate : (k : ℕ) → (T.Node k → K) → K
  | 0, H => H T.root
  | k + 1, H => evaluate k (E.collapse k H)

@[simp] theorem evaluate_zero (H : T.Node 0 → K) :
    E.evaluate 0 H = H T.root := rfl

@[simp] theorem evaluate_succ (k : ℕ) (H : T.Node (k + 1) → K) :
    E.evaluate (k + 1) H = E.evaluate k (E.collapse k H) := rfl

/-- Evaluate only between the two indicated depths. -/
noncomputable def evaluateFrom (k : ℕ) :
    (d : ℕ) → (T.Node (k + d) → K) → T.Node k → K
  | 0, H => H
  | d + 1, H => evaluateFrom k d (E.collapse (k + d) H)

@[simp] theorem evaluateFrom_zero (k : ℕ) (H : T.Node k → K) :
    E.evaluateFrom k 0 H = H := rfl

@[simp] theorem evaluateFrom_succ (k d : ℕ) (H : T.Node (k + (d + 1)) → K) :
    E.evaluateFrom k (d + 1) H =
      E.evaluateFrom k d (E.collapse (k + d) H) := rfl

/-- Evaluation factorizes at every intermediate cutoff. -/
theorem evaluate_factorization (k d : ℕ) (H : T.Node (k + d) → K) :
    E.evaluate (k + d) H = E.evaluate k (E.evaluateFrom k d H) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      exact ih (E.collapse (k + d) H)

/-- A finite weighted average has the expected weighted sensitivity. -/
theorem childAverage_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  classical
  rw [E.childAverage_val, E.childAverage_val, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c • ((H c : X) - H' c)‖ ≤
        ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
          ‖W.weight k c • ((H c : X) - H' c)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (W.weight_pos k c)]

/-- Each actual parent map is nonexpansive after taking its child average. -/
theorem collapse_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  have hm : ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ := by
    simpa only [collapse, Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (E.nonexpansive k p).dist_le_mul (E.childAverage k H p)
        (E.childAverage k H' p)
  exact hm.trans (E.childAverage_norm_sub_le k H H' p)

/-- The sensitivity estimate for actual nonlinear root outputs. -/
theorem evaluate_norm_sub_le (k : ℕ) (H H' : T.Node k → K) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  classical
  induction k with
  | zero =>
      have hsingle : (Finset.univ : Finset (T.Node 0)) = {T.root} := by
        ext v
        simp [T.eq_root v]
      simp [evaluate, hsingle, WeightedTree.pathWeight]
  | succ k ih =>
      calc
        ‖(E.evaluate (k + 1) H : X) - E.evaluate (k + 1) H'‖ ≤
            ∑ p, W.pathWeight k p *
              ‖(E.collapse k H p : X) - E.collapse k H' p‖ :=
          ih (E.collapse k H) (E.collapse k H')
        _ ≤ ∑ p, W.pathWeight k p *
            ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
              W.weight k c * ‖(H c : X) - H' c‖ := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (E.collapse_norm_sub_le k H H' p)
            (le_of_lt (W.pathWeight_pos k p))
        _ = ∑ p, ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
            W.pathWeight k (T.parent k c) * W.weight k c *
              ‖(H c : X) - H' c‖ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          have hcp := (Finset.mem_filter.mp hc).2
          rw [hcp, mul_assoc]
        _ = ∑ c, W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖ := by
          rw [Finset.sum_fiberwise]
          rfl

/-- Uniform cutoff errors propagate with no increase to the root. -/
theorem evaluate_norm_sub_le_of_forall (k : ℕ) (H H' : T.Node k → K)
    {ε : ℝ} (hε : ∀ v, ‖(H v : X) - H' v‖ ≤ ε) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤ ε := by
  calc
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
        ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ :=
      E.evaluate_norm_sub_le k H H'
    _ ≤ ∑ v, W.pathWeight k v * ε := by
      exact Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (hε v) (le_of_lt (W.pathWeight_pos k v))
    _ = ε := by rw [← Finset.sum_mul, W.sum_pathWeight, one_mul]

/-- Changing just one cutoff output has its actual path weight as sensitivity. -/
theorem evaluate_norm_sub_le_single (k : ℕ) (H H' : T.Node k → K)
    (v : T.Node k) (heq : ∀ w, w ≠ v → H w = H' w) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  classical
  refine (E.evaluate_norm_sub_le k H H').trans_eq ?_
  apply Finset.sum_eq_single v
  · intro w hw hwv
    rw [heq w hwv, sub_self, norm_zero, mul_zero]
  · simp

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

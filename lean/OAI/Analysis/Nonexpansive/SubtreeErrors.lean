import OAI.Analysis.Nonexpansive.SubtreeEvaluation
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-!
Errors of the actual nonlinear subtree evaluation.

An untouched subtree is compared to its map applied to the anchor. The proof
uses the actual collapse rule and child-average estimates at each internal
level. The local version follows from equality on descendant leaves.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Averaging a constant child assignment returns the same actual point. -/
@[simp] theorem childAverage_const (k : ℕ) (b : K) (p : T.Node k) :
    E.childAverage k (fun _ => b) p = b := by
  apply Subtype.ext
  rw [E.childAverage_val, ← Finset.sum_smul, W.weight_sum, one_smul]

/-- Each assigned map is nonexpansive in the original ambient norm. -/
theorem map_norm_sub_le (k : ℕ) (p : T.Node k) (a b : K) :
    ‖(E.map k p a : X) - E.map k p b‖ ≤ ‖(a : X) - b‖ := by
  simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    using (E.nonexpansive k p).dist_le_mul a b

/-- One actual collapse transmits a constant up to the node's displacement. -/
theorem collapse_norm_sub_point_le (k : ℕ) (H : T.Node (k + 1) → K)
    (b : K) (p : T.Node k) :
    ‖(E.collapse k H p : X) - b‖ ≤
      (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - b‖) + ‖(E.map k p b : X) - b‖ := by
  have hcompare : ‖(E.collapse k H p : X) - E.map k p b‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - b‖ := by
    simpa only [collapse, E.childAverage_const] using
      E.collapse_norm_sub_le k H (fun _ => b) p
  calc
    ‖(E.collapse k H p : X) - b‖ ≤
        ‖(E.collapse k H p : X) - E.map k p b‖ +
          ‖(E.map k p b : X) - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add_left hcompare _

/-- Compare an actual parent output to the parent's prescribed anchor label. -/
theorem collapse_norm_sub_label_le (k : ℕ) (H : T.Node (k + 1) → K)
    (x : K) (p : T.Node k) :
    ‖(E.collapse k H p : X) - E.map k p x‖ ≤
      (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - E.map (k + 1) c x‖) +
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ := by
  calc
    ‖(E.collapse k H p : X) - E.map k p x‖ ≤
        ‖(E.collapse k H p : X) -
          E.collapse k (fun c => E.map (k + 1) c x) p‖ +
        ‖(E.collapse k (fun c => E.map (k + 1) c x) p : X) -
          E.map k p x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add
      (E.collapse_norm_sub_le k H (fun c => E.map (k + 1) c x) p)
      (E.map_norm_sub_le k p
        (E.childAverage k (fun c => E.map (k + 1) c x) p) x)

/-- The canonical untouched subtree incurs the sum of its finite level errors. -/
theorem subtreeOutput_labels_norm_sub_le (x : K) (τ : ℕ → ℝ) {N : ℕ}
    (haverage : ∀ k, k < N → ∀ p : T.Node k,
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ ≤ τ k)
    {k : ℕ} (h : k ≤ N) (v : T.Node k) :
    ‖(E.subtreeOutput h (fun s => E.map N s x) v : X) - E.map k v x‖ ≤
      ∑ d ∈ Finset.Ico k N, τ d := by
  classical
  induction h using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
      rw [E.subtreeOutput_top_step (Nat.le_of_lt hk) hk]
      calc
        ‖(E.collapse k (E.subtreeOutput hk (fun s => E.map N s x)) v : X) -
            E.map k v x‖ ≤
            (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = v),
              W.weight k c *
                ‖(E.subtreeOutput hk (fun s => E.map N s x) c : X) -
                  E.map (k + 1) c x‖) + τ k :=
          (E.collapse_norm_sub_label_le k
            (E.subtreeOutput hk (fun s => E.map N s x)) x v).trans
            (add_le_add_right (haverage k hk v) _)
        _ ≤ (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = v),
              W.weight k c * (∑ d ∈ Finset.Ico (k + 1) N, τ d)) + τ k := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left (ih c) (W.weight_nonneg k c)
        _ = (∑ d ∈ Finset.Ico (k + 1) N, τ d) + τ k := by
          rw [← Finset.sum_mul, W.weight_sum, one_mul]
        _ = ∑ d ∈ Finset.Ico k N, τ d := by
          rw [Finset.sum_eq_sum_Ico_succ_bot hk τ]
          exact add_comm _ _

/-- Only descendant leaves need be untouched; all other leaf states are arbitrary. -/
theorem subtreeOutput_untouched_norm_sub_le (x : K) (τ : ℕ → ℝ) {N : ℕ}
    (haverage : ∀ k, k < N → ∀ p : T.Node k,
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ ≤ τ k)
    {k : ℕ} (h : k ≤ N) (H : T.Node N → K) (v : T.Node k)
    (huntouched : ∀ s, T.ancestorLE h s = v → H s = E.map N s x) :
    ‖(E.subtreeOutput h H v : X) - E.map k v x‖ ≤
      ∑ d ∈ Finset.Ico k N, τ d := by
  rw [E.subtreeOutput_congr h H (fun s => E.map N s x) v huntouched]
  exact E.subtreeOutput_labels_norm_sub_le x τ haverage h v

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

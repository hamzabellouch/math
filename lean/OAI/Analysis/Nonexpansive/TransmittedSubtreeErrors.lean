import OAI.Analysis.Nonexpansive.SubtreeEvaluation
import OAI.Analysis.Nonexpansive.SubtreeErrors

namespace OAI

/-!
# Error transmitted from constant terminal values

Every map displacement is counted at its actual node, with its actual path
weight.  The proof follows the concrete finite evaluator.  No positive
uniform lower bound on the weights and no affine property of the node maps
is needed.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Regroup the weighted children of the descendants at one level. -/
theorem sum_descendant_weighted_children {k n : ℕ} (h : k ≤ n)
    (v : T.Node k) (f : T.Node (n + 1) → ℝ) :
    (∑ p ∈ T.descendants h v, W.pathWeight n p *
      (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c)) =
      ∑ c ∈ T.descendants (Nat.le_succ_of_le h) v, W.pathWeight (n + 1) c * f c := by
  classical
  calc
    _ = ∑ p, (if T.ancestorLE h p = v then W.pathWeight n p else 0) *
        (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c) := by
      simp only [OrderedTree.descendants, Finset.sum_filter, ite_mul, zero_mul]
    _ = ∑ c, (if T.ancestorLE h (T.parent n c) = v then
        W.pathWeight n (T.parent n c) else 0) * (W.weight n c * f c) :=
      sum_fiber_mul (T.parent n)
        (fun p => if T.ancestorLE h p = v then W.pathWeight n p else 0)
        (fun c => W.weight n c * f c)
    _ = _ := by
      simp only [OrderedTree.descendants, Finset.sum_filter,
        T.ancestorLE_step_apply h, WeightedTree.pathWeight_succ,
        ite_mul, zero_mul, mul_assoc]

/-- The actual path weight times subtree sensitivity is bounded by the
weighted cutoff errors on that subtree's own descendants. -/
theorem subtreeOutput_scaled_norm_sub_le {k N : ℕ} (h : k ≤ N) :
    ∀ (H H' : T.Node N → K) (v : T.Node k),
      W.pathWeight k v *
          ‖(E.subtreeOutput h H v : X) - E.subtreeOutput h H' v‖ ≤
        ∑ s ∈ T.descendants h v, W.pathWeight N s * ‖(H s : X) - H' s‖ := by
  classical
  induction h using Nat.leRec with
  | refl =>
      intro H H' v
      have hdesc : T.descendants (Nat.le_refl k) v = {v} := by
        ext s
        simp only [T.mem_descendants, T.ancestorLE_refl_apply, Finset.mem_singleton]
      simpa only [E.subtreeOutput_refl_apply, hdesc, Finset.sum_singleton] using
        (le_refl (W.pathWeight k v * ‖(H v : X) - H' v‖))
  | @le_succ_of_le N h ih =>
      intro H H' v
      rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
      calc
        _ ≤ ∑ p ∈ T.descendants h v, W.pathWeight N p *
            ‖(E.collapse N H p : X) - E.collapse N H' p‖ :=
          ih (E.collapse N H) (E.collapse N H') v
        _ ≤ ∑ p ∈ T.descendants h v, W.pathWeight N p *
            (∑ c ∈ Finset.univ.filter (fun c => T.parent N c = p),
              W.weight N c * ‖(H c : X) - H' c‖) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (E.collapse_norm_sub_le N H H' p)
            (W.pathWeight_nonneg N p)
        _ = _ := sum_descendant_weighted_children (W := W) h v
          (fun c => ‖(H c : X) - H' c‖)

/-- The unweighted displacement of all maps strictly above terminal depth. -/
noncomputable def terminalDefect (N : ℕ) (b : K) : ℝ :=
  ∑ d ∈ Finset.range N, ∑ v : T.Node d, ‖(E.map d v b : X) - b‖

/-- Weighted map displacement on one level below a specified ancestor.
Levels before the ancestor contribute zero. -/
noncomputable def descendantLevelDefect {k : ℕ} (v : T.Node k) (b : K)
    (d : ℕ) : ℝ := by
  classical
  exact if hd : k ≤ d then
    ∑ s ∈ T.descendants hd v, W.pathWeight d s * ‖(E.map d s b : X) - b‖
  else 0

/-- The exact finite weighted sum over internal descendants of a node. -/
noncomputable def internalDescendantDefect {k : ℕ} (N : ℕ) (b : K)
    (v : T.Node k) : ℝ :=
  ∑ d ∈ Finset.range N, E.descendantLevelDefect v b d

@[simp] theorem internalDescendantDefect_self (k : ℕ) (b : K) (v : T.Node k) :
    E.internalDescendantDefect k b v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  simp only [descendantLevelDefect, dite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hd))]

theorem internalDescendantDefect_succ {k N : ℕ} (h : k ≤ N) (b : K)
    (v : T.Node k) :
    E.internalDescendantDefect (N + 1) b v = E.internalDescendantDefect N b v +
      ∑ s ∈ T.descendants h v, W.pathWeight N s * ‖(E.map N s b : X) - b‖ := by
  classical
  simp only [internalDescendantDefect, Finset.sum_range_succ,
    descendantLevelDefect, dite_eq_left h]

/-- Every descendant path weight is at most its ancestor's path weight. -/
theorem descendantLevelDefect_le {k : ℕ} (v : T.Node k) (b : K) (d : ℕ) :
    E.descendantLevelDefect v b d ≤
      W.pathWeight k v * ∑ s : T.Node d, ‖(E.map d s b : X) - b‖ := by
  classical
  unfold descendantLevelDefect
  split_ifs with hd
  · rw [OrderedTree.descendants, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    by_cases hancestor : T.ancestorLE hd s = v
    · rw [ite_eq_left hancestor]
      have hweight : W.pathWeight d s ≤ W.pathWeight k v := by
        simpa only [hancestor] using W.pathWeight_le_ancestor hd s
      exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    · rw [ite_eq_right hancestor]
      exact mul_nonneg (W.pathWeight_nonneg k v) (norm_nonneg _)
  · exact mul_nonneg (W.pathWeight_nonneg k v)
      (Finset.sum_nonneg fun s _ => norm_nonneg _)

/-- Summing the ancestor-weight comparisons gives the full unweighted
terminal displacement budget, multiplied by just the ancestor's weight. -/
theorem internalDescendantDefect_le {k : ℕ} (N : ℕ) (b : K) (v : T.Node k) :
    E.internalDescendantDefect N b v ≤ W.pathWeight k v * E.terminalDefect N b := by
  classical
  unfold internalDescendantDefect terminalDefect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  exact E.descendantLevelDefect_le v b d

/-- Exact scaled transmitted bound for a constant terminal assignment. -/
theorem subtreeOutput_const_scaled_norm_sub_le {k N : ℕ} (h : k ≤ N)
    (b : K) (v : T.Node k) :
    W.pathWeight k v * ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ ≤
      E.internalDescendantDefect N b v := by
  classical
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le N h ih =>
      rw [E.subtreeOutput_step h, E.internalDescendantDefect_succ h]
      have hs : W.pathWeight k v *
          ‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
            E.subtreeOutput h (fun _ => b) v‖ ≤
          ∑ s ∈ T.descendants h v,
            W.pathWeight N s * ‖(E.map N s b : X) - b‖ := by
        simpa only [collapse, E.childAverage_const] using
          E.subtreeOutput_scaled_norm_sub_le h
            (E.collapse N (fun _ => b)) (fun _ => b) v
      calc
        _ ≤ W.pathWeight k v *
            (‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
                E.subtreeOutput h (fun _ => b) v‖ +
              ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _)
            (W.pathWeight_nonneg k v)
        _ = W.pathWeight k v *
            ‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
              E.subtreeOutput h (fun _ => b) v‖ +
            W.pathWeight k v * ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ :=
          mul_add _ _ _
        _ ≤ (∑ s ∈ T.descendants h v,
            W.pathWeight N s * ‖(E.map N s b : X) - b‖) +
              E.internalDescendantDefect N b v := add_le_add hs ih
        _ = _ := add_comm _ _

/-- Dividing by the positive weight gives the weighted
internal-descendant error formula. -/
theorem subtreeOutput_const_norm_sub_le_quotient {k N : ℕ} (h : k ≤ N)
    (b : K) (v : T.Node k) :
    ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ ≤
      E.internalDescendantDefect N b v / W.pathWeight k v := by
  apply (le_div_iff₀ (W.pathWeight_pos k v)).2
  simpa only [mul_comm] using E.subtreeOutput_const_scaled_norm_sub_le h b v

/-- Constant terminal error is at most the total unweighted displacement.
Only positivity of this one path weight is used to cancel it. -/
theorem subtreeOutput_const_norm_sub_le_terminalDefect {k N : ℕ} (h : k ≤ N)
    (b : K) (v : T.Node k) :
    ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ ≤ E.terminalDefect N b := by
  exact (mul_le_mul_iff_right₀ (W.pathWeight_pos k v)).mp
    ((E.subtreeOutput_const_scaled_norm_sub_le h b v).trans
      (E.internalDescendantDefect_le N b v))

/-- The scaled bound only needs constant terminal values below this node. -/
theorem subtreeOutput_scaled_norm_sub_le_of_descendants_eq {k N : ℕ} (h : k ≤ N)
    (H : T.Node N → K) (b : K) (v : T.Node k)
    (heq : ∀ s ∈ T.descendants h v, H s = b) :
    W.pathWeight k v * ‖(E.subtreeOutput h H v : X) - b‖ ≤
      E.internalDescendantDefect N b v := by
  rw [E.subtreeOutput_congr_of_descendants h H (fun _ => b) v heq]
  exact E.subtreeOutput_const_scaled_norm_sub_le h b v

/-- A completely switched subtree has error bounded by the common terminal
budget, regardless of all terminal values outside that subtree. -/
theorem subtreeOutput_norm_sub_le_terminalDefect {k N : ℕ} (h : k ≤ N)
    (H : T.Node N → K) (b : K) (v : T.Node k)
    (heq : ∀ s ∈ T.descendants h v, H s = b) :
    ‖(E.subtreeOutput h H v : X) - b‖ ≤ E.terminalDefect N b := by
  rw [E.subtreeOutput_congr_of_descendants h H (fun _ => b) v heq]
  exact E.subtreeOutput_const_norm_sub_le_terminalDefect h b v

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

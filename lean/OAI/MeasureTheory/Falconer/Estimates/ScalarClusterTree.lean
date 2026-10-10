import OAI.MeasureTheory.Falconer.Recursion.ScalarTerminalProjection

namespace OAI

/-! Separated cluster trees retain all leaves in each terminal fiber.
 Their common terminal cardinality multiplies every level of the gain. -/
namespace Falconer

structure ScalarClusterTree (δ : ℝ) (N : ℕ) where
  nodes : ℕ → Finset ℝ
  children : ℕ → ℝ → Finset ℝ
  points : ℕ → ℝ → Finset ℝ
  branching : ℕ → ℕ
  radius : ℕ → ℝ
  gap : ℕ → ℝ
  branch_pos : ∀ n < N, 0 < branching n
  radius_ge : ∀ n < N, δ ≤ radius n
  gap_pos : ∀ n < N, 0 < gap n
  gap_gt : ∀ n < N, 5*radius n < gap n
  child_subset : ∀ n < N, ∀ x ∈ nodes (n+1), children n x ⊆ nodes n
  child_card : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).card = branching n
  child_sep : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ y ∈ children n x,
    ∀ z ∈ children n x, y ≠ z → gap n ≤ |y-z|
  child_bound : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ y ∈ children n x,
    ∀ a ∈ points n y, |a-y| ≤ radius n
  parent_eq : ∀ n < N, ∀ x ∈ nodes (n+1), points (n+1) x = (children n x).biUnion (points n)
  leaf_size : ℕ
  leaf_pos : 0 < leaf_size
  leaf_card : ∀ x ∈ nodes 0, (points 0 x).card = leaf_size
  leaf_sep : ∀ x ∈ nodes 0, ∀ u ∈ points 0 x, ∀ v ∈ points 0 x,
    u ≠ v → δ ≤ |u-v|

 theorem ScalarClusterTree.child_nonempty {δ : ℝ} {N : ℕ} (T : ScalarClusterTree δ N)
    {n : ℕ} (hn : n < N) {x : ℝ} (hx : x ∈ T.nodes (n+1)) :
    (T.children n x).Nonempty := by
  rw [← Finset.card_pos,T.child_card n hn x hx]
  exact T.branch_pos n hn

 theorem ScalarClusterTree.points_card {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (T : ScalarClusterTree δ N) :
    ∀ n ≤ N, ∀ x ∈ T.nodes n,
      (T.points n x).card = T.leaf_size*(∏ j ∈ Finset.range n, T.branching j) := by
  classical
  intro n hn
  induction n with
  | zero => intro x hx; simpa using T.leaf_card x hx
  | succ n ih =>
    intro x hx
    have hnN : n < N := by omega
    have hr0 : 0 < T.radius n := hδ.trans_le (T.radius_ge n hnN)
    have hd : (T.children n x : Set ℝ).PairwiseDisjoint (T.points n) := by
      intro y hy z hz hyz
      apply Finset.disjoint_left.mpr
      intro a hay haz
      have h1 := T.child_bound n hnN x hx y hy a hay
      have h2 := T.child_bound n hnN x hx z hz a haz
      have hs := T.child_sep n hnN x hx y hy z hz hyz
      have ht : |y-z| ≤ |a-y|+|a-z| := by
        calc
          |y-z| ≤ |y-a|+|a-z| := abs_sub_le _ _ _
          _ = _ := by rw [abs_sub_comm y a]
      have hg := T.gap_gt n hnN
      linarith
    rw [T.parent_eq n hnN x hx,Finset.card_biUnion hd]
    calc
      _ = ∑ _y ∈ T.children n x, T.leaf_size*(∏ j ∈ Finset.range n, T.branching j) :=
        Finset.sum_congr rfl (fun y hy => ih (by omega) y (T.child_subset n hnN x hx hy))
      _ = _ := by simp [T.child_card n hnN x hx,Finset.prod_range_succ,Nat.mul_comm,Nat.mul_assoc]

 theorem ScalarClusterTree.points_nonempty {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (T : ScalarClusterTree δ N) {n : ℕ} (hn : n ≤ N) {x : ℝ} (hx : x ∈ T.nodes n) :
    (T.points n x).Nonempty := by
  apply Finset.card_pos.mp
  rw [T.points_card hδ n hn x hx]
  exact Nat.mul_pos T.leaf_pos (Finset.prod_pos (fun j hj =>
    T.branch_pos j (lt_of_lt_of_le (Finset.mem_range.mp hj) hn)))

end Falconer

end OAI

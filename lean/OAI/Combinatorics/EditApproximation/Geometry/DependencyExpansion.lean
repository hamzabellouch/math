import OAI.Combinatorics.EditApproximation.Geometry.Work

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

def dependencyWordCount (same earlier r s : ℕ) : ℕ :=
  (r + s).choose r * same ^ r * earlier ^ s

theorem dependencyWordCount_succ (a b r s : ℕ) :
    dependencyWordCount a b (r + 1) (s + 1) =
      a * dependencyWordCount a b r (s + 1) + b * dependencyWordCount a b (r + 1) s := by
  unfold dependencyWordCount
  rw [show r + 1 + (s + 1) = (r + s + 1) + 1 by omega, Nat.choose_succ_succ']
  rw [show r + (s + 1) = r + s + 1 by omega, show r + 1 + s = r + s + 1 by omega]
  simp only [pow_succ]
  ring

theorem dependencyPathBudget_mono (d k D K a b : ℕ) (hd : d ≤ D) (hk : k ≤ K) :
    dependencyPathBudget d k a b ≤ dependencyPathBudget D K a b := by
  unfold dependencyPathBudget
  apply le_trans (sum_le_sum_of_subset (range_mono (Nat.add_le_add_right hd 1)))
  apply sum_le_sum
  intro r hr
  exact sum_le_sum_of_subset (range_mono (Nat.add_le_add_right hk 1))

theorem dependencyPathBudget_zero_zero (a b : ℕ) : dependencyPathBudget 0 0 a b = 1 := by
  simp [dependencyPathBudget]

theorem dependencyPathBudget_succ_zero (d a b : ℕ) :
    dependencyPathBudget (d + 1) 0 a b = 1 + a * dependencyPathBudget d 0 a b := by
  simp only [dependencyPathBudget, zero_add, sum_range_one, add_zero, Nat.choose_self,
    one_mul, pow_zero, mul_one]
  rw [sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← sum_mul]
  ring

theorem dependencyPathBudget_zero_succ (k a b : ℕ) :
    dependencyPathBudget 0 (k + 1) a b = 1 + b * dependencyPathBudget 0 k a b := by
  simp only [dependencyPathBudget, zero_add, sum_range_one, Nat.choose_zero_right,
    pow_zero, one_mul]
  rw [sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← sum_mul]
  ring

theorem dependencyPathBudget_succ_succ (d k a b : ℕ) :
    dependencyPathBudget (d + 1) (k + 1) a b =
      1 + a * dependencyPathBudget d (k + 1) a b +
        b * dependencyPathBudget (d + 1) k a b := by
  have hpascal (r s : ℕ) := dependencyWordCount_succ a b r s
  have hleft (r : ℕ) : dependencyWordCount a b (r + 1) 0 =
      a * dependencyWordCount a b r 0 := by
    simp [dependencyWordCount, pow_succ, Nat.mul_comm]
  have hright (s : ℕ) : dependencyWordCount a b 0 (s + 1) =
      b * dependencyWordCount a b 0 s := by
    simp [dependencyWordCount, pow_succ, Nat.mul_comm]
  have hzero : dependencyWordCount a b 0 0 = 1 := by simp [dependencyWordCount]
  have hsplit (r : ℕ) : (∑ s ∈ range (k + 2), dependencyWordCount a b r s) =
      dependencyWordCount a b r 0 + ∑ s ∈ range (k + 1), dependencyWordCount a b r (s + 1) := by
    rw [sum_range_succ']
    ring
  change (∑ r ∈ range (d + 2), ∑ s ∈ range (k + 2), dependencyWordCount a b r s) =
    1 + a * (∑ r ∈ range (d + 1), ∑ s ∈ range (k + 2), dependencyWordCount a b r s) +
      b * (∑ r ∈ range (d + 2), ∑ s ∈ range (k + 1), dependencyWordCount a b r s)
  rw [sum_range_succ' (fun r => ∑ s ∈ range (k + 2), dependencyWordCount a b r s) (d + 1),
    sum_range_succ' (fun r => ∑ s ∈ range (k + 1), dependencyWordCount a b r s) (d + 1)]
  simp_rw [hsplit]
  simp_rw [hpascal, sum_add_distrib, ← mul_sum]
  simp_rw [hleft, hright, hzero, ← mul_sum]
  ring

theorem dependencyPathBudget_recurrence (d k a b : ℕ) :
    dependencyPathBudget d k a b = 1 +
      (if d = 0 then 0 else a * dependencyPathBudget (d - 1) k a b) +
      (if k = 0 then 0 else b * dependencyPathBudget d (k - 1) a b) := by
  cases d with
  | zero =>
    cases k with
    | zero => simp [dependencyPathBudget_zero_zero]
    | succ k => simpa using dependencyPathBudget_zero_succ k a b
  | succ d =>
    cases k with
    | zero => simpa using dependencyPathBudget_succ_zero d a b
    | succ k => simpa using dependencyPathBudget_succ_succ d k a b

/-- Node labels carry remaining physical depth and remaining rank.
Children in the first and second arrays have distinct edge sorts. -/
inductive DependencyExpansion where
  | node (depth rank sameCount earlierCount : ℕ)
      (sameChildren : Fin sameCount → DependencyExpansion)
      (earlierChildren : Fin earlierCount → DependencyExpansion) : DependencyExpansion

namespace DependencyExpansion

def depth : DependencyExpansion → ℕ
  | .node d _ _ _ _ _ => d

def rank : DependencyExpansion → ℕ
  | .node _ k _ _ _ _ => k

def nodeCount : DependencyExpansion → ℕ
  | .node _ _ _ _ same earlier => 1 + (∑ i, nodeCount (same i)) + ∑ i, nodeCount (earlier i)

/-- Every same edge strictly decreases physical depth and never increases
rank. Every earlier edge strictly decreases rank and never increases depth.
No global count is part of this certificate. -/
def Valid (a b : ℕ) : DependencyExpansion → Prop
  | .node d k m n same earlier =>
      m ≤ a ∧ n ≤ b ∧
      (∀ i, (same i).depth < d ∧ (same i).rank ≤ k ∧ Valid a b (same i)) ∧
      (∀ i, (earlier i).depth ≤ d ∧ (earlier i).rank < k ∧ Valid a b (earlier i))

theorem nodeCount_le_budget (a b : ℕ) (tree : DependencyExpansion) (h : Valid a b tree) :
    tree.nodeCount ≤ dependencyPathBudget tree.depth tree.rank a b := by
  revert h
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h
    obtain ⟨hm, hn, hs, he⟩ := h
    have hsame : (∑ i, (same i).nodeCount) ≤
        if d = 0 then 0 else a * dependencyPathBudget (d - 1) k a b := by
      by_cases hd : d = 0
      · have hempty : m = 0 := by
          by_contra hm0
          have hbad := (hs ⟨0, Nat.pos_of_ne_zero hm0⟩).1
          omega
        subst m
        simp [hd]
      · rw [ite_eq_right hd]
        calc
          (∑ i, (same i).nodeCount) ≤ ∑ _ : Fin m, dependencyPathBudget (d - 1) k a b := by
            apply sum_le_sum
            intro i hi
            exact (ihs i (hs i).2.2).trans (dependencyPathBudget_mono _ _ _ _ a b
              (by have hp := (hs i).1; omega) (hs i).2.1)
          _ = m * dependencyPathBudget (d - 1) k a b := by simp
          _ ≤ a * dependencyPathBudget (d - 1) k a b := Nat.mul_le_mul_right _ hm
    have hearlier : (∑ i, (earlier i).nodeCount) ≤
        if k = 0 then 0 else b * dependencyPathBudget d (k - 1) a b := by
      by_cases hk : k = 0
      · have hempty : n = 0 := by
          by_contra hn0
          have hbad := (he ⟨0, Nat.pos_of_ne_zero hn0⟩).2.1
          omega
        subst n
        simp [hk]
      · rw [ite_eq_right hk]
        calc
          (∑ i, (earlier i).nodeCount) ≤ ∑ _ : Fin n, dependencyPathBudget d (k - 1) a b := by
            apply sum_le_sum
            intro i hi
            exact (ihe i (he i).2.2).trans (dependencyPathBudget_mono _ _ _ _ a b
              (he i).1 (by have hp := (he i).2.1; omega))
          _ = n * dependencyPathBudget d (k - 1) a b := by simp
          _ ≤ b * dependencyPathBudget d (k - 1) a b := Nat.mul_le_mul_right _ hn
    change 1 + (∑ i, (same i).nodeCount) + (∑ i, (earlier i).nodeCount) ≤
      dependencyPathBudget d k a b
    rw [dependencyPathBudget_recurrence]
    exact Nat.add_le_add (Nat.add_le_add_left hsame 1) hearlier

theorem nodeCount_le_budget_of_le (a b D K : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hd : tree.depth ≤ D) (hk : tree.rank ≤ K) :
    tree.nodeCount ≤ dependencyPathBudget D K a b :=
  (nodeCount_le_budget a b tree h).trans
    (dependencyPathBudget_mono _ _ _ _ a b hd hk)

/-- Literal count of nodes whose remaining physical depth is at least
`floor`. Descendants are inspected even when the current node fails the
test; pruning below the threshold is a consequence of `Valid`. -/
def nodeCountAtOrAbove (floor : ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier =>
      (if floor ≤ d then 1 else 0) +
        (∑ i, nodeCountAtOrAbove floor (same i)) +
        ∑ i, nodeCountAtOrAbove floor (earlier i)

/-- Literal count of nodes at one remaining physical depth. -/
def nodeCountAtDepth (target : ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier =>
      (if d = target then 1 else 0) +
        (∑ i, nodeCountAtDepth target (same i)) +
        ∑ i, nodeCountAtDepth target (earlier i)

theorem nodeCountAtOrAbove_eq_zero (a b floor : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hd : tree.depth < floor) :
    nodeCountAtOrAbove floor tree = 0 := by
  revert h hd
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h hd
    obtain ⟨hm, hn, hs, he⟩ := h
    change d < floor at hd
    change (if floor ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove floor (same i)) +
      (∑ i, nodeCountAtOrAbove floor (earlier i)) = 0
    have hsame : ∀ i, nodeCountAtOrAbove floor (same i) = 0 := by
      intro i
      exact ihs i (hs i).2.2 (lt_trans (hs i).1 hd)
    have hearlier : ∀ i, nodeCountAtOrAbove floor (earlier i) = 0 := by
      intro i
      exact ihe i (he i).2.2 (lt_of_le_of_lt (he i).1 hd)
    simp [Nat.not_le.mpr hd, hsame, hearlier]

/-- The path budget for a depth threshold uses only the available descent
above that threshold, independently of the total depth of the expansion. -/
theorem nodeCountAtOrAbove_le_budget (a b floor : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) :
    nodeCountAtOrAbove floor tree ≤
      dependencyPathBudget (tree.depth - floor) tree.rank a b := by
  revert h
  induction tree generalizing floor with
  | node d k m n same earlier ihs ihe =>
    intro h
    by_cases hfloor : d < floor
    · have hzero := nodeCountAtOrAbove_eq_zero a b floor
        (.node d k m n same earlier) h hfloor
      rw [hzero]
      exact Nat.zero_le _
    obtain ⟨hm, hn, hs, he⟩ := h
    have hfd : floor ≤ d := Nat.le_of_not_gt hfloor
    have hsame : (∑ i, nodeCountAtOrAbove floor (same i)) ≤
        if d - floor = 0 then 0
        else a * dependencyPathBudget (d - floor - 1) k a b := by
      by_cases hd : d - floor = 0
      · have hzero : ∀ i, nodeCountAtOrAbove floor (same i) = 0 := by
          intro i
          apply nodeCountAtOrAbove_eq_zero a b floor (same i) (hs i).2.2
          have hp := (hs i).1
          omega
        simp [hd, hzero]
      · rw [ite_eq_right hd]
        calc
          (∑ i, nodeCountAtOrAbove floor (same i)) ≤
              ∑ _ : Fin m, dependencyPathBudget (d - floor - 1) k a b := by
            apply sum_le_sum
            intro i hi
            exact (ihs i floor (hs i).2.2).trans
              (dependencyPathBudget_mono _ _ _ _ a b
                (by have hp := (hs i).1; omega) (hs i).2.1)
          _ = m * dependencyPathBudget (d - floor - 1) k a b := by simp
          _ ≤ a * dependencyPathBudget (d - floor - 1) k a b :=
            Nat.mul_le_mul_right _ hm
    have hearlier : (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤
        if k = 0 then 0 else b * dependencyPathBudget (d - floor) (k - 1) a b := by
      by_cases hk : k = 0
      · have hempty : n = 0 := by
          by_contra hn0
          have hbad := (he ⟨0, Nat.pos_of_ne_zero hn0⟩).2.1
          omega
        subst n
        simp [hk]
      · rw [ite_eq_right hk]
        calc
          (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤
              ∑ _ : Fin n, dependencyPathBudget (d - floor) (k - 1) a b := by
            apply sum_le_sum
            intro i hi
            exact (ihe i floor (he i).2.2).trans
              (dependencyPathBudget_mono _ _ _ _ a b
                (Nat.sub_le_sub_right (he i).1 floor)
                (by have hp := (he i).2.1; omega))
          _ = n * dependencyPathBudget (d - floor) (k - 1) a b := by simp
          _ ≤ b * dependencyPathBudget (d - floor) (k - 1) a b :=
            Nat.mul_le_mul_right _ hn
    change (if floor ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove floor (same i)) +
      (∑ i, nodeCountAtOrAbove floor (earlier i)) ≤ dependencyPathBudget (d - floor) k a b
    rw [ite_eq_left hfd, dependencyPathBudget_recurrence]
    exact Nat.add_le_add (Nat.add_le_add_left hsame 1) hearlier

theorem nodeCountAtDepth_le_atOrAbove (target : ℕ) (tree : DependencyExpansion) :
    nodeCountAtDepth target tree ≤ nodeCountAtOrAbove target tree := by
  induction tree with
  | node d k m n same earlier ihs ihe =>
    change (if d = target then 1 else 0) +
      (∑ i, nodeCountAtDepth target (same i)) +
      (∑ i, nodeCountAtDepth target (earlier i)) ≤
      (if target ≤ d then 1 else 0) +
      (∑ i, nodeCountAtOrAbove target (same i)) +
      (∑ i, nodeCountAtOrAbove target (earlier i))
    apply Nat.add_le_add
    · apply Nat.add_le_add
      · split_ifs <;> omega
      · exact sum_le_sum (fun i hi => ihs i)
    · exact sum_le_sum (fun i hi => ihe i)

/-- All nodes reached with physical descent at most `j`, including those
reached through earlier-index edges that themselves decrease depth. -/
def nodeCountThroughDescent (j : ℕ) (tree : DependencyExpansion) : ℕ :=
  nodeCountAtOrAbove (tree.depth - j) tree

/-- Nodes at physical descent exactly `j`. -/
def layerNodeCount (j : ℕ) (tree : DependencyExpansion) : ℕ :=
  if j ≤ tree.depth then nodeCountAtDepth (tree.depth - j) tree else 0

theorem nodeCountThroughDescent_le_budget (a b j K : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hk : tree.rank ≤ K) :
    nodeCountThroughDescent j tree ≤ dependencyPathBudget j K a b := by
  exact (nodeCountAtOrAbove_le_budget a b (tree.depth - j) tree h).trans
    (dependencyPathBudget_mono _ _ _ _ a b (by omega) hk)

theorem layerNodeCount_le_throughDescent (j : ℕ) (tree : DependencyExpansion) :
    layerNodeCount j tree ≤ nodeCountThroughDescent j tree := by
  unfold layerNodeCount nodeCountThroughDescent
  split_ifs
  · exact nodeCountAtDepth_le_atOrAbove _ tree
  · exact Nat.zero_le _

theorem layerNodeCount_le_budget (a b j K : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hk : tree.rank ≤ K) :
    layerNodeCount j tree ≤ dependencyPathBudget j K a b :=
  (layerNodeCount_le_throughDescent j tree).trans
    (nodeCountThroughDescent_le_budget a b j K tree h hk)

theorem nodeCountAtDepth_sum (a b D : ℕ) (tree : DependencyExpansion)
    (h : Valid a b tree) (hd : tree.depth ≤ D) :
    (∑ t ∈ range (D + 1), nodeCountAtDepth t tree) = tree.nodeCount := by
  revert h hd
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h hd
    obtain ⟨hm, hn, hs, he⟩ := h
    change d ≤ D at hd
    have hroot : (∑ t ∈ range (D + 1), if d = t then 1 else 0) = 1 := by
      simp [mem_range.mpr (Nat.lt_succ_of_le hd)]
    have hsame : (∑ t ∈ range (D + 1), ∑ i, nodeCountAtDepth t (same i)) =
        ∑ i, (same i).nodeCount := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihs i (hs i).2.2 (le_trans (Nat.le_of_lt (hs i).1) hd)
    have hearlier : (∑ t ∈ range (D + 1), ∑ i, nodeCountAtDepth t (earlier i)) =
        ∑ i, (earlier i).nodeCount := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihe i (he i).2.2 (le_trans (he i).1 hd)
    change (∑ t ∈ range (D + 1), ((if d = t then 1 else 0) +
      (∑ i, nodeCountAtDepth t (same i)) +
      (∑ i, nodeCountAtDepth t (earlier i)))) =
      1 + (∑ i, (same i).nodeCount) + ∑ i, (earlier i).nodeCount
    rw [sum_add_distrib, sum_add_distrib, hroot, hsame, hearlier]

/-- The actual layers partition the expansion. This lets weighted
initial-state charges be summed layer by layer without using the total
depth bound for every layer. -/
theorem layerNodeCount_sum (a b : ℕ) (tree : DependencyExpansion) (h : Valid a b tree) :
    (∑ j ∈ range (tree.depth + 1), layerNodeCount j tree) = tree.nodeCount := by
  calc
    (∑ j ∈ range (tree.depth + 1), layerNodeCount j tree) =
        ∑ j ∈ range (tree.depth + 1), nodeCountAtDepth (tree.depth - j) tree := by
      apply sum_congr rfl
      intro j hj
      exact ite_eq_left (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = ∑ j ∈ range (tree.depth + 1), nodeCountAtDepth j tree := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun j => nodeCountAtDepth j tree) (tree.depth + 1)
    _ = tree.nodeCount := nodeCountAtDepth_sum a b tree.depth tree h le_rfl

/-- Charge every actual node by a function of its remaining physical
depth, as needed for length-dependent initial-state evaluation. -/
def depthWeightedCount (weight : ℕ → ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier => weight d +
      (∑ i, depthWeightedCount weight (same i)) +
      ∑ i, depthWeightedCount weight (earlier i)

theorem depthWeightedCount_eq_depth_sum (a b D : ℕ) (weight : ℕ → ℕ)
    (tree : DependencyExpansion) (h : Valid a b tree) (hd : tree.depth ≤ D) :
    (∑ t ∈ range (D + 1), nodeCountAtDepth t tree * weight t) =
      depthWeightedCount weight tree := by
  revert h hd
  induction tree with
  | node d k m n same earlier ihs ihe =>
    intro h hd
    obtain ⟨hm, hn, hs, he⟩ := h
    change d ≤ D at hd
    have hroot : (∑ t ∈ range (D + 1), (if d = t then 1 else 0) * weight t) = weight d := by
      simp [ite_mul, mem_range.mpr (Nat.lt_succ_of_le hd)]
    have hsame : (∑ t ∈ range (D + 1), (∑ i, nodeCountAtDepth t (same i)) * weight t) =
        ∑ i, depthWeightedCount weight (same i) := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihs i (hs i).2.2 (le_trans (Nat.le_of_lt (hs i).1) hd)
    have hearlier : (∑ t ∈ range (D + 1), (∑ i, nodeCountAtDepth t (earlier i)) * weight t) =
        ∑ i, depthWeightedCount weight (earlier i) := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      exact ihe i (he i).2.2 (le_trans (he i).1 hd)
    change (∑ t ∈ range (D + 1), ((if d = t then 1 else 0) +
      (∑ i, nodeCountAtDepth t (same i)) +
      (∑ i, nodeCountAtDepth t (earlier i))) * weight t) =
      weight d + (∑ i, depthWeightedCount weight (same i)) +
        ∑ i, depthWeightedCount weight (earlier i)
    simp_rw [add_mul, sum_add_distrib]
    rw [hroot, hsame, hearlier]

theorem depthWeightedCount_eq_layer_sum (a b : ℕ) (weight : ℕ → ℕ)
    (tree : DependencyExpansion) (h : Valid a b tree) :
    depthWeightedCount weight tree =
      ∑ j ∈ range (tree.depth + 1), layerNodeCount j tree * weight (tree.depth - j) := by
  symm
  calc
    (∑ j ∈ range (tree.depth + 1), layerNodeCount j tree * weight (tree.depth - j)) =
        ∑ j ∈ range (tree.depth + 1),
          nodeCountAtDepth (tree.depth - j) tree * weight (tree.depth - j) := by
      apply sum_congr rfl
      intro j hj
      rw [layerNodeCount, ite_eq_left (Nat.le_of_lt_succ (mem_range.mp hj))]
    _ = ∑ t ∈ range (tree.depth + 1), nodeCountAtDepth t tree * weight t := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun t => nodeCountAtDepth t tree * weight t) (tree.depth + 1)
    _ = depthWeightedCount weight tree :=
      depthWeightedCount_eq_depth_sum a b tree.depth weight tree h le_rfl

/-- Unfold actual finite successor arrays. Local progress makes the
construction terminate even when earlier edges also descend physically. -/
def build {ι : Type*} (d r m n : ι → ℕ)
    (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
    (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
    (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x) (root : ι) : DependencyExpansion :=
  .node (d root) (r root) (m root) (n root)
    (fun i => build d r m n s e hs he (s root i))
    (fun i => build d r m n s e hs he (e root i))
termination_by d root + r root
decreasing_by
  · exact Nat.add_lt_add_of_lt_of_le (hs root i).1 (hs root i).2
  · exact Nat.add_lt_add_of_le_of_lt (he root i).1 (he root i).2

section Builder

variable {ι : Type*} (d r m n : ι → ℕ)
  (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
  (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
  (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x)

theorem build_depth (root : ι) : (build d r m n s e hs he root).depth = d root := by
  rw [build]
  rfl

theorem build_rank (root : ι) : (build d r m n s e hs he root).rank = r root := by
  rw [build]
  rfl

theorem build_valid (a b : ℕ) (hm : ∀ x, m x ≤ a) (hn : ∀ x, n x ≤ b) (root : ι) :
    Valid a b (build d r m n s e hs he root) := by
  have hall : ∀ fuel x, d x + r x = fuel → Valid a b (build d r m n s e hs he x) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro x hx
      rw [build]
      refine ⟨hm x, hn x, ?_, ?_⟩
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [build_depth]
          exact (hs x i).1
        · rw [build_rank]
          exact (hs x i).2
        · apply ih (d (s x i) + r (s x i)) _ (s x i) rfl
          rw [← hx]
          exact Nat.add_lt_add_of_lt_of_le (hs x i).1 (hs x i).2
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [build_depth]
          exact (he x i).1
        · rw [build_rank]
          exact (he x i).2
        · apply ih (d (e x i) + r (e x i)) _ (e x i) rfl
          rw [← hx]
          exact Nat.add_lt_add_of_le_of_lt (he x i).1 (he x i).2
  exact hall (d root + r root) root rfl

/-- A global node bound derived directly from actual successor arrays,
their two local cardinality bounds, and their local progress proofs. -/
theorem build_nodeCount_le (a b : ℕ) (hm : ∀ x, m x ≤ a) (hn : ∀ x, n x ≤ b) (root : ι) :
    (build d r m n s e hs he root).nodeCount ≤ dependencyPathBudget (d root) (r root) a b := by
  simpa only [build_depth, build_rank] using
    nodeCount_le_budget a b _ (build_valid d r m n s e hs he a b hm hn root)

theorem build_layerNodeCount_le (a b j K : ℕ)
    (hm : ∀ x, m x ≤ a) (hn : ∀ x, n x ≤ b) (root : ι) (hk : r root ≤ K) :
    layerNodeCount j (build d r m n s e hs he root) ≤ dependencyPathBudget j K a b := by
  apply layerNodeCount_le_budget a b j K _ (build_valid d r m n s e hs he a b hm hn root)
  simpa only [build_rank] using hk

end Builder

end DependencyExpansion
end EditApproximation

end OAI

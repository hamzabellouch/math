import OAI.Combinatorics.GraphThreshold.ProbabilityTreePaths

namespace OAI

/-! Deterministic removal of initial zero-capacity levels. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai.ProbabilityTree

variable {X : Type}

/-- Choose one child deterministically from the actual nonempty child law. -/
def firstChild : {d : ℕ} → ProbabilityTree X (d + 1) → ProbabilityTree X d
  | _, @node _ _ _ _ law _ _ child => child (Classical.choice (branch_nonempty law))

def firstLabel : {d : ℕ} → ProbabilityTree X (d + 1) → Finset X
  | _, @node _ _ _ _ law _ label _ => label (Classical.choice (branch_nonempty law))

/-- Prepend the chosen incoming arc to a path of the chosen child. -/
def prependChosen : {d : ℕ} → (T : ProbabilityTree X (d + 1)) →
    (firstChild T).Path → T.Path
  | _, @node _ _ _ _ law _ _ _, p => ⟨Classical.choice (branch_nonempty law), p⟩

/-- Remove `k` initial levels. The additive depth form avoids subtraction casts. -/
def drop : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → ProbabilityTree X d
  | 0, _, T => T
  | k + 1, _, T => drop k (firstChild T)

/-- Lift a retained path through the fixed choices on the removed prefix. -/
def liftDropPath : (k : ℕ) → {d : ℕ} → (T : ProbabilityTree X (d + k)) →
    (drop k T).Path → T.Path
  | 0, _, _, p => p
  | k + 1, _, T, p => prependChosen T (liftDropPath k (firstChild T) p)

/-- Reindex a tree along equality of depths, without changing its data. -/
def castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) : ProbabilityTree X e := h ▸ T

def castPath {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    T.Path ≃ (castDepth h T).Path := by
  cases h
  exact Equiv.refl _

/-- Subtraction-indexed convenience wrapper for removing an initial prefix. -/
def dropPrefix {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d) :
    ProbabilityTree X (d - k) :=
  drop k (castDepth (Nat.sub_add_cancel hk).symm T)

def liftDropPrefixPath {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d)
    (p : (dropPrefix T k hk).Path) : T.Path :=
  (castPath (Nat.sub_add_cancel hk).symm T).symm
    (liftDropPath k (castDepth (Nat.sub_add_cancel hk).symm T) p)

section Properties

variable [DecidableEq X]

theorem pathUnion_prependChosen {d : ℕ} (T : ProbabilityTree X (d + 1))
    (p : (firstChild T).Path) :
    T.pathUnion (prependChosen T p) = firstLabel T ∪ (firstChild T).pathUnion p := by
  cases T
  rfl

theorem firstChild_support_subset {d : ℕ} (T : ProbabilityTree X (d + 1)) :
    (firstChild T).support ⊆ T.support := by
  cases T with
  | node B law positive label child =>
      exact child_support_subset law positive label child _

theorem firstChild_isDisjoint {d : ℕ} {T : ProbabilityTree X (d + 1)}
    (hT : T.IsDisjoint) : (firstChild T).IsDisjoint := by
  cases T
  exact hT.2 _

omit [DecidableEq X] in
theorem firstChild_hasCapacities {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstChild T).HasCapacities (fun i => m (i + 1)) := by
  cases T
  exact hT.2 _

theorem firstChild_hasSpread {d : ℕ} {T : ProbabilityTree X (d + 1)} {a : ℕ → ℝ}
    (hT : T.HasSpread a) : (firstChild T).HasSpread (fun i => a (i + 1)) := by
  cases T
  exact hT.2 _

omit [DecidableEq X] in
theorem firstLabel_card_le {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstLabel T).card ≤ m 0 := by
  cases T
  exact hT.1 _

omit [DecidableEq X] in
theorem firstLabel_eq_empty {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (hm : m 0 = 0) : firstLabel T = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := firstLabel_card_le hT
  omega

/-- Labels committed by the deterministic choices on the removed prefix. -/
def prefixUnion : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → Finset X
  | 0, _, _ => ∅
  | k + 1, _, T => firstLabel T ∪ prefixUnion k (firstChild T)

theorem pathUnion_liftDropPath (k : ℕ) {d : ℕ} (T : ProbabilityTree X (d + k))
    (p : (drop k T).Path) :
    T.pathUnion (liftDropPath k T p) = prefixUnion k T ∪ (drop k T).pathUnion p := by
  induction k generalizing d with
  | zero => simp [liftDropPath, prefixUnion, drop]
  | succ k ih =>
      change T.pathUnion (prependChosen T (liftDropPath k T.firstChild p)) =
        (T.firstLabel ∪ prefixUnion k T.firstChild) ∪ (drop k T.firstChild).pathUnion p
      rw [pathUnion_prependChosen, ih T.firstChild p, Finset.union_assoc]

theorem drop_support_subset (k : ℕ) {d : ℕ} (T : ProbabilityTree X (d + k)) :
    (drop k T).support ⊆ T.support := by
  induction k generalizing d with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact (ih (firstChild T)).trans (firstChild_support_subset T)

theorem drop_isDisjoint (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    (hT : T.IsDisjoint) : (drop k T).IsDisjoint := by
  induction k generalizing d with
  | zero => exact hT
  | succ k ih => exact ih (firstChild_isDisjoint hT)

omit [DecidableEq X] in
theorem drop_hasCapacities (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) :
    (drop k T).HasCapacities (fun i => m (i + k)) := by
  induction k generalizing d m with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasCapacities hT)

theorem drop_hasSpread (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {a : ℕ → ℝ} (hT : T.HasSpread a) :
    (drop k T).HasSpread (fun i => a (i + k)) := by
  induction k generalizing d a with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasSpread hT)

theorem prefixUnion_eq_empty_of_capacities (k : ℕ) {d : ℕ}
    {T : ProbabilityTree X (d + k)} {m : ℕ → ℕ} (hT : T.HasCapacities m)
    (hm : ∀ i, i < k → m i = 0) : prefixUnion k T = ∅ := by
  induction k generalizing d m with
  | zero => rfl
  | succ k ih =>
      rw [prefixUnion, firstLabel_eq_empty hT (hm 0 (by omega)), Finset.empty_union]
      exact ih (firstChild_hasCapacities hT) (fun i hi => hm (i + 1) (by omega))

/-- Removing zero-capacity levels preserves every retained full path union exactly. -/
theorem pathUnion_liftDropPath_eq (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) (hm : ∀ i, i < k → m i = 0)
    (p : (drop k T).Path) : T.pathUnion (liftDropPath k T p) = (drop k T).pathUnion p := by
  rw [pathUnion_liftDropPath, prefixUnion_eq_empty_of_capacities k hT hm, Finset.empty_union]

@[simp] theorem support_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).support = T.support := by cases h; rfl

@[simp] theorem isDisjoint_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).IsDisjoint ↔ T.IsDisjoint := by cases h; rfl

omit [DecidableEq X] in
@[simp] theorem hasCapacities_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (m : ℕ → ℕ) : (castDepth h T).HasCapacities m ↔ T.HasCapacities m := by cases h; rfl

@[simp] theorem hasSpread_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (a : ℕ → ℝ) : (castDepth h T).HasSpread a ↔ T.HasSpread a := by cases h; rfl

theorem pathUnion_castPath_symm {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (p : (castDepth h T).Path) :
    T.pathUnion ((castPath h T).symm p) = (castDepth h T).pathUnion p := by cases h; rfl

theorem dropPrefix_support_subset {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).support ⊆ T.support := by
  simpa only [dropPrefix, support_castDepth] using
    drop_support_subset k (castDepth (Nat.sub_add_cancel hk).symm T)

theorem dropPrefix_isDisjoint {d : ℕ} {T : ProbabilityTree X d} (hT : T.IsDisjoint)
    (k : ℕ) (hk : k ≤ d) : (dropPrefix T k hk).IsDisjoint := by
  apply drop_isDisjoint
  simpa using hT

omit [DecidableEq X] in
theorem dropPrefix_hasCapacities {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasCapacities (fun i => m (i + k)) := by
  apply drop_hasCapacities
  simpa using hT

theorem dropPrefix_hasSpread {d : ℕ} {T : ProbabilityTree X d} {a : ℕ → ℝ}
    (hT : T.HasSpread a) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasSpread (fun i => a (i + k)) := by
  apply drop_hasSpread
  simpa using hT

/-- Every path after zero-prefix trimming is an original full path with exactly the same union. -/
theorem pathUnion_liftDropPrefixPath_eq {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d)
    (hm : ∀ i, i < k → m i = 0) (p : (dropPrefix T k hk).Path) :
    T.pathUnion (liftDropPrefixPath T k hk p) = (dropPrefix T k hk).pathUnion p := by
  unfold liftDropPrefixPath
  rw [pathUnion_castPath_symm]
  apply pathUnion_liftDropPath_eq k _ hm
  simpa using hT

theorem coveredBy_of_dropPrefix {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d)
    (hm : ∀ i, i < k → m i = 0) {W : Finset X}
    (hW : (dropPrefix T k hk).CoveredBy W) : T.CoveredBy W := by
  obtain ⟨p, hp⟩ := hW
  refine ⟨liftDropPrefixPath T k hk p, ?_⟩
  rwa [pathUnion_liftDropPrefixPath_eq hT k hk hm p]

end Properties

end LeanBlast.SecondKahnKalai.ProbabilityTree

end

end OAI

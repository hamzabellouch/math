import OAI.Combinatorics.EditApproximation.Geometry.PartitionIntervals
import OAI.Combinatorics.EditApproximation.Geometry.BalancedIntervals
import OAI.Combinatorics.EditApproximation.Geometry.SourcePrefixes

namespace OAI

/-!
# Actual optimal child states

The alignment split is converted to bounded target endpoint states at
the actual balanced source children. Its sum is exactly the parent
edit distance; its target endpoints are shared.
-/

namespace EditApproximation

open EditDistortion Finset

theorem zipWith_sum_ofFn {α β γ : Type*} [AddCommMonoid γ]
    {M : ℕ} (f : α → β → γ) (x : Fin M → α) (y : Fin M → β) :
    (List.zipWith f (List.ofFn x) (List.ofFn y)).sum = ∑ i, f (x i) (y i) := by
  have hlist : List.zipWith f (List.ofFn x) (List.ofFn y) =
      List.ofFn (fun i => f (x i) (y i)) := by
    apply List.ext_getElem
    · simp only [List.length_zipWith, List.length_ofFn, min_self]
    · intro i hi hj
      simp only [List.getElem_zipWith, List.getElem_ofFn]
  rw [hlist, List.sum_ofFn]

theorem optimal_balanced_child_states {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) :
    ∃ states : Fin M → TargetInterval target.length,
      (∑ i, stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i)) =
          stateEditCost (substring source parent.lo parent.hi) target q ∧
      (states ⟨0, hM⟩).lo = q.lo ∧
      (states ⟨M - 1, by omega⟩).hi = q.hi ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      ∀ i : Fin M,
        Nat.dist (q.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤
          stateEditCost (substring source parent.lo parent.hi) target q ∧
        Nat.dist (q.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤
          stateEditCost (substring source parent.lo parent.hi) target q := by
  let parts := List.ofFn fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  have hpartsLength : parts.length = M := List.length_ofFn
  have hnonempty : parts ≠ [] := by intro h; have hl := congrArg List.length h; simp [hpartsLength] at hl; omega
  obtain ⟨targets, hlen, hflat, hcost⟩ := edit_partition_split parts hnonempty
    (substring target q.lo q.hi)
  have htargetsLength : targets.length = M := hlen.trans hpartsLength
  let states : Fin M → TargetInterval target.length := fun i =>
    partitionInterval target q targets hflat ⟨i.val, by omega⟩
  have hsource : parts.flatten = substring source parent.lo parent.hi :=
    sourceChild_partition source hM parent
  refine ⟨states, ?_, ?_, ?_, ?_, ?_⟩
  · have htargets : List.ofFn (fun i : Fin M => targets[i.val]'(by omega)) = targets := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, htargetsLength]
      · intro i hi hj
        simp only [List.getElem_ofFn]
    have hsum : (∑ i : Fin M, edit
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        (targets[i.val]'(by omega))) = edit parts.flatten (substring target q.lo q.hi) := by
      rw [← zipWith_sum_ofFn, htargets]
      exact hcost
    rw [hsource] at hsum
    convert hsum using 1
    · apply sum_congr rfl
      intro i hi
      change edit _ (substring target (partitionInterval target q targets hflat _).lo
        (partitionInterval target q targets hflat _).hi) = _
      rw [partitionInterval_substring]
    · rfl
  · simp only [states, partitionInterval, List.take_zero, List.flatten_nil,
      List.length_nil, Nat.add_zero]
  · have hlast : M - 1 + 1 = targets.length := by omega
    have hlength := congrArg List.length hflat
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] at hlength
    change q.lo + (targets.take (M - 1 + 1)).flatten.length = q.hi
    rw [hlast, List.take_length]
    have horder := q.ordered
    omega
  · intro i j hnext
    exact partitionInterval_shared target q targets hflat _ _ hnext
  · have hprefixBound (j : ℕ) :
        Nat.dist (q.lo + (parts.take j).flatten.length)
          (q.lo + (targets.take j).flatten.length) ≤
            stateEditCost (substring source parent.lo parent.hi) target q := by
      have h := optimal_partition_anchor_shift_bound parts targets
        (substring target q.lo q.hi) hlen.symm hcost j
      rw [natural_distance_cast] at h
      have hnat : Nat.dist (targets.take j).flatten.length (parts.take j).flatten.length ≤
          edit parts.flatten (substring target q.lo q.hi) := by exact_mod_cast h
      rw [hsource] at hnat
      change Nat.dist _ _ ≤ edit (substring source parent.lo parent.hi) (substring target q.lo q.hi)
      unfold Nat.dist at hnat ⊢
      omega
    intro i
    constructor
    · have h := hprefixBound i.val
      dsimp only [parts] at h
      rw [sourceChildren_prefix_length source hM parent i.val (by omega)] at h
      exact h
    · have h := hprefixBound (i.val + 1)
      dsimp only [parts] at h
      rw [sourceChildren_prefix_length source hM parent (i.val + 1) (by omega)] at h
      exact h

end EditApproximation

end OAI

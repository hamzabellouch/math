import OAI.Combinatorics.EditApproximation.Binary.BinaryGeometrySpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem prefixReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (j : ℕ) (p : BinaryFraction)
    (h : ∀ i, allocation i (states i) ≤ (read i (states i)).2) :
    prefixReadAllocation parent r states read allocation j p ≤
      (prefixReadWithWork parent r states read j p).2 := by
  let words := (arithmeticMapWithWork (fun i : Fin M =>
    if i.val < j then read i (states i) else (zero, 1)) (List.finRange M)).1
  let finish := (canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p).1
  have hw := arithmeticMapAllocation_le_work
    (fun i : Fin M => if i.val < j then read i (states i) else (zero, 1))
    (fun i : Fin M => if i.val < j then allocation i (states i) else 0) (List.finRange M) (by
      intro i _
      split_ifs
      · exact h i
      · exact Nat.zero_le _)
  have hf := canonicalAddAllocation_le_work (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
  have hc := connectionAllocation_le_work (nat r.lo) finish ((List.ofFn states).take j)
  have hs := sumListAllocation_le_work words
  have ha := canonicalAddAllocation_le_work
    (connectionWithWork (nat r.lo) finish ((List.ofFn states).take j)).1 (sumListWithWork words).1
  unfold prefixReadAllocation prefixReadWithWork
  dsimp only [words, finish] at hc hs ha ⊢
  omega



theorem prefixMinimumReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (j : ℕ) (p : BinaryFraction)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    prefixMinimumReadAllocation parent r actions hne read allocation j p ≤
      (prefixMinimumReadWithWork parent r actions hne read j p).2 := by
  have hf := prefixReadAllocation_le_work parent r (actions.head hne) read allocation j p
    (h _ (List.head_mem hne))
  have hs := arithmeticMapAllocation_le_work
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixReadAllocation parent r action read allocation j p) actions
    (fun action ha => prefixReadAllocation_le_work parent r action read allocation j p (h action ha))
  have hm := minimumAllocation_le_work (prefixReadWithWork parent r (actions.head hne) read j p).1
    (arithmeticMapWithWork (fun action => prefixReadWithWork parent r action read j p) actions).1
  unfold prefixMinimumReadAllocation prefixMinimumReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI

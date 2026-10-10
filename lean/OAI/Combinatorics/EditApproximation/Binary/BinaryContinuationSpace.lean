import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem onlineMinimumAllocation_le_work (values : List BinaryFraction) :
    onlineMinimumAllocation values ≤ (onlineMinimumWithWork values).2 := by
  cases values with
  | nil => exact Nat.zero_le _
  | cons first rest => exact (minimumAllocation_le_work first rest).trans (Nat.le_add_right _ _)



theorem refinementUpdateAllocation_le_work (delta cone : BinaryFraction) (online : Option BinaryFraction) :
    refinementUpdateAllocation delta cone online ≤ (refinementUpdateWithWork delta cone online).2 := by
  cases online with
  | none => exact Nat.zero_le _
  | some online =>
    have ha := canonicalAddAllocation_le_work one delta
    have hd := divAllocation_le_work cone (canonicalAddWithWork one delta).1
    have hm := maxAllocation_le_work (divWithWork cone (canonicalAddWithWork one delta).1).1 online
    have hf := minAllocation_le_work cone
      (maxWithWork (divWithWork cone (canonicalAddWithWork one delta).1).1 online).1
    unfold refinementUpdateAllocation refinementUpdateWithWork
    dsimp only
    omega

/-- The two Bellman passes, materialized online scores and final arithmetic
retain their actual primitive allocation traces. -/


theorem localContinuationReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L delta fallback : BinaryFraction) (old current : Child → BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Child → ℕ) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M))
    (hd : ∀ state, distanceAllocation query state ≤ (distance query state).2)
    (ho : ∀ child, oldAllocation child ≤ (old child).2)
    (hc : ∀ child, currentAllocation child ≤ (current child).2) :
    localContinuationReadAllocation distance distanceAllocation L delta fallback old current
      oldAllocation currentAllocation query wide groups online ≤
      (localContinuationReadWithWork distance L delta fallback old current query wide groups online).2 := by
  have hw := bellmanReadAllocation_le_work distance distanceAllocation L fallback old oldAllocation query wide
    (fun action _ => hd action.center) (fun action _ i => ho (action.childState i))
  have hg := bellmanReadAllocation_le_work distance distanceAllocation L
    (bellmanReadWithWork distance L fallback old query wide).1 current currentAllocation query groups
    (fun action _ => hd action.center) (fun action _ i => hc (action.childState i))
  have hs := arithmeticMapAllocation_le_work (bellmanActionReadWithWork distance L current query)
    (bellmanActionReadAllocation distance distanceAllocation L current currentAllocation query) online
    (fun action _ => bellmanActionReadAllocation_le_work distance distanceAllocation L current
      currentAllocation query action (hd action.center) (fun i => hc (action.childState i)))
  let scores := (arithmeticMapWithWork (bellmanActionReadWithWork distance L current query) online).1
  have hm := onlineMinimumAllocation_le_work scores
  have hf := refinementUpdateAllocation_le_work delta
    (bellmanReadWithWork distance L (bellmanReadWithWork distance L fallback old query wide).1 current query groups).1
    (onlineMinimumWithWork scores).1
  unfold localContinuationReadAllocation localContinuationReadWithWork
  dsimp only [scores] at hm hf ⊢
  omega

end EditApproximation.BinaryFraction

end OAI

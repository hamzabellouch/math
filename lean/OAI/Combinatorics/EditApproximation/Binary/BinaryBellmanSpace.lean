import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryGeometrySpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Actual temporary cells allocated while scoring one action; child values
are retained pointers and their lookup scratch is counted by `footprint`. -/


theorem bellmanActionReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L : BinaryFraction) (read : Child → BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (action : BinaryBellmanAction Parent Child M)
    (hd : distanceAllocation query action.center ≤ (distance query action.center).2)
    (hr : ∀ i, footprint (action.childState i) ≤ (read (action.childState i)).2) :
    bellmanActionReadAllocation distance distanceAllocation L read footprint query action ≤
      (bellmanActionReadWithWork distance L read query action).2 := by
  have hw := arithmeticMapAllocation_le_work (fun i => read (action.childState i))
    (fun i => footprint (action.childState i)) (List.finRange M) (fun i _ => hr i)
  have hm := canonicalMulAllocation_le_work L (distance query action.center).1
  have ha := canonicalAddAllocation_le_work (canonicalMulWithWork L (distance query action.center).1).1 action.connection
  let words := (arithmeticMapWithWork (fun i => read (action.childState i)) (List.finRange M)).1
  have hs := sumListAllocation_le_work words
  have hf := canonicalAddAllocation_le_work
    (canonicalAddWithWork (canonicalMulWithWork L (distance query action.center).1).1 action.connection).1
    (sumListWithWork words).1
  unfold bellmanActionReadAllocation bellmanActionReadWithWork
  dsimp only [words] at hs hf ⊢
  omega



theorem bellmanReadAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L fallback : BinaryFraction) (read : Child → BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (actions : List (BinaryBellmanAction Parent Child M))
    (hd : ∀ action ∈ actions, distanceAllocation query action.center ≤ (distance query action.center).2)
    (hr : ∀ action ∈ actions, ∀ i, footprint (action.childState i) ≤ (read (action.childState i)).2) :
    bellmanReadAllocation distance distanceAllocation L fallback read footprint query actions ≤
      (bellmanReadWithWork distance L fallback read query actions).2 := by
  have hs := arithmeticMapAllocation_le_work (bellmanActionReadWithWork distance L read query)
    (bellmanActionReadAllocation distance distanceAllocation L read footprint query) actions
    (fun action ha => bellmanActionReadAllocation_le_work distance distanceAllocation L read footprint
      query action (hd action ha) (hr action ha))
  have hm := minimumAllocation_le_work fallback
    (arithmeticMapWithWork (bellmanActionReadWithWork distance L read query) actions).1
  unfold bellmanReadAllocation bellmanReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI

import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

def groupMemberAllocation {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) : ℕ :=
  let terms := (arithmeticMapWithWork (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)).1
  arithmeticMapAllocation (fun s => groupScaleAllocation (count s) (scales s) envelope values (draw s)) (List.finRange T) +
    sumListAllocation terms + canonicalAddAllocation connection (sumListWithWork terms).1

theorem groupMemberAllocation_le_work {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) :
    groupMemberAllocation scales count connection envelope values draw ≤
      (groupMemberWithWork scales count connection envelope values draw).2 := by
  let terms := (arithmeticMapWithWork (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)).1
  have ht := arithmeticMapAllocation_le_work
    (fun s => groupScaleWithWork (count s) (scales s) envelope values (draw s))
    (fun s => groupScaleAllocation (count s) (scales s) envelope values (draw s)) (List.finRange T)
    (fun s _ => groupScaleAllocation_le_work (count s) (scales s) envelope values (draw s))
  have hs := sumListAllocation_le_work terms
  have ha := canonicalAddAllocation_le_work connection (sumListWithWork terms).1
  unfold groupMemberAllocation groupMemberWithWork
  dsimp only [terms] at hs ha ⊢
  omega

def countedGroupMemberAllocation {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) : ℕ :=
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  let heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  vectorMapAllocation T (fun t => groupSampleCountAllocation M Q b (scales t)) +
    groupMemberAllocation scales count connection envelope values (fun t j => draw t (Fin.cast (heq t) j))

theorem countedGroupMemberAllocation_le_work {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) :
    countedGroupMemberAllocation Q b scales connection envelope values draw ≤
      (countedGroupMemberWithWork Q b scales connection envelope values draw).2 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  have hc := vectorMapAllocation_le_work T (fun t => groupSampleCountWithWork M Q b (scales t))
    (fun t => groupSampleCountAllocation M Q b (scales t)) (fun t => groupSampleCountAllocation_le_work M Q b (scales t))
  have hg := groupMemberAllocation_le_work scales count connection envelope values (fun t j => draw t (Fin.cast (heq t) j))
  unfold countedGroupMemberAllocation countedGroupMemberWithWork
  dsimp only [count, counts] at hg ⊢
  omega



theorem selectGroupAllocation_le_work {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) (allocation : ι → ℕ)
    (h : ∀ member ∈ members, allocation member ≤ (estimate member).2) :
    selectGroupAllocation members estimate allocation ≤ (selectGroupWithWork members hne estimate).2 := by
  have hs := scoredArgmaxAllocation_le_work
    (fun member => ((estimate member).1.neg, (estimate member).2 + 1)) allocation members
    (fun member hm => (h member hm).trans (Nat.le_succ _))
  unfold selectGroupAllocation selectGroupWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI

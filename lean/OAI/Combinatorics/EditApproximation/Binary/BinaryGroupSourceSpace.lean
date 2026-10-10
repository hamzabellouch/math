import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupReductionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupMemberSource
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Index decoding, the sampled index spine and the exact/sample reduction. -/


theorem groupScaleSourceAllocation_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ)
    (allocation : Fin k → ℕ) (ha : ∀ i, allocation i ≤ (draw i).2) :
    groupScaleSourceAllocation k h envelope values draw allocation ≤
      (groupScaleSourceWithWork k h envelope values draw).2 := by
  let indices := if k = M then (List.finRange M, 0) else arithmeticMapWithWork draw (List.finRange k)
  have hi := groupIndexAllocation_le_work h envelope values indices.1
  have hm := arithmeticMapAllocation_le_work draw allocation (List.finRange k) (fun i _ => ha i)
  have hd := divAllocation_le_work (nat M) (nat k)
  have hp := canonicalMulAllocation_le_work
    (if k = M then (one, 1) else divWithWork (nat M) (nat k)).1
    (groupIndexWithWork h envelope values indices.1).1
  unfold groupScaleSourceAllocation groupScaleSourceWithWork
  dsimp only [indices] at hi hp
  dsimp only
  by_cases heq : k = M
  · simp only [ite_eq_left heq] at hi hp ⊢
    omega
  · simp only [ite_eq_right heq] at hi hp ⊢
    omega



theorem groupMemberSourceAllocation_le_work {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ)
    (allocation : ∀ s : Fin T, Fin (count s) → ℕ)
    (ha : ∀ s i, allocation s i ≤ (draw s i).2) :
    groupMemberSourceAllocation scales count connection envelope values draw allocation ≤
      (groupMemberSourceWithWork scales count connection envelope values draw).2 := by
  let terms := (arithmeticMapWithWork (fun s => groupScaleSourceWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)).1
  have ht := arithmeticMapAllocation_le_work
    (fun s => groupScaleSourceWithWork (count s) (scales s) envelope values (draw s))
    (fun s => groupScaleSourceAllocation (count s) (scales s) envelope values (draw s) (allocation s)) (List.finRange T)
    (fun s _ => groupScaleSourceAllocation_le_work (count s) (scales s) envelope values (draw s) (allocation s) (ha s))
  have hs := sumListAllocation_le_work terms
  have ha := canonicalAddAllocation_le_work connection (sumListWithWork terms).1
  unfold groupMemberSourceAllocation groupMemberSourceWithWork
  dsimp only [terms] at hs ha ⊢
  omega



theorem countedGroupMemberSourceAllocation_le_work {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
    (allocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)
    (ha : ∀ t i, allocation t i ≤ (draw t i).2) :
    countedGroupMemberSourceAllocation Q b scales connection envelope values draw allocation ≤
      (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).2 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  have hc := vectorMapAllocation_le_work T (fun t => groupSampleCountWithWork M Q b (scales t))
    (fun t => groupSampleCountAllocation M Q b (scales t)) (fun t => groupSampleCountAllocation_le_work M Q b (scales t))
  have hg := groupMemberSourceAllocation_le_work scales count connection envelope values (fun t j => draw t (Fin.cast (heq t) j))
    (fun t j => allocation t (Fin.cast (heq t) j)) (fun t j => ha t _)
  unfold countedGroupMemberSourceAllocation countedGroupMemberSourceWithWork
  dsimp only [count, counts] at hg ⊢
  omega


end EditApproximation.BinaryFraction

end OAI

import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSourcePort
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadCostBounds
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

namespace BinaryFraction



theorem groupMemberSourceWithWork_value {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) :
    (groupMemberSourceWithWork scales count connection envelope values draw).1 =
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).1 := by
  simp only [groupMemberSourceWithWork, groupMemberWithWork, arithmeticMapWithWork_value,
    groupScaleSourceWithWork_value]

theorem groupMemberSourceWithWork_eq_cost {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) (R : ℕ)
    (hr : ∀ s i, (draw s i).2 ≤ R) :
    (groupMemberSourceWithWork scales count connection envelope values draw).1 =
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).1 ∧
    (groupMemberSourceWithWork scales count connection envelope values draw).2 ≤
      (groupMemberWithWork scales count connection envelope values (fun s i => (draw s i).1)).2 * (R + 4) := by
  have hm := arithmeticMapWithWork_factor
    (fun s => groupScaleSourceWithWork (count s) (scales s) envelope values (draw s))
    (fun s => groupScaleWithWork (count s) (scales s) envelope values (fun i => (draw s i).1))
    (List.finRange T) (R + 4) (by omega)
    (fun s _ => groupScaleSourceWithWork_value _ _ _ _ _)
    (fun s _ => groupScaleSourceWithWork_cost _ _ _ _ _ R (hr s))
  unfold groupMemberSourceWithWork groupMemberWithWork
  dsimp only
  rw [hm.1]
  exact ⟨rfl, by nlinarith only [hm.2]⟩



theorem groupMemberSourceWithWork_transport {M T : ℕ}
    (scales : Fin T → BinaryFraction) (left right : Fin T → ℕ) (h : ∀ t, left t = right t)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (right t) → Fin M × ℕ) :
    groupMemberSourceWithWork scales left connection envelope values (fun t j => draw t (Fin.cast (h t) j)) =
      groupMemberSourceWithWork scales right connection envelope values draw := by
  have heq : left = right := funext h
  subst right
  rfl

theorem countedGroupMemberSourceWithWork_eq_cost {M T : ℕ} (Q b : ℕ)
    (scales : Fin T → BinaryFraction) (connection : BinaryFraction)
    (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
    (R : ℕ) (hr : ∀ t i, (draw t i).2 ≤ R) :
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).1 =
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).1 ∧
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).2 ≤
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).2 * (R + 4) := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  have hm := groupMemberSourceWithWork_eq_cost scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j)) R (fun t j => hr t _)
  unfold countedGroupMemberSourceWithWork countedGroupMemberWithWork
  dsimp only
  change _ = (groupMemberWithWork scales count connection envelope values
    (fun t j => (draw t (Fin.cast (heq t) j)).1)).1 ∧ _
  rw [hm.1]
  exact ⟨rfl, by nlinarith only [hm.2]⟩

theorem countedGroupMemberSourceWithWork_value {M T : ℕ} (Q b : ℕ)
    (scales : Fin T → BinaryFraction) (connection : BinaryFraction)
    (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ) :
    (countedGroupMemberSourceWithWork Q b scales connection envelope values draw).1 =
      (countedGroupMemberWithWork Q b scales connection envelope values (fun t i => (draw t i).1)).1 := by
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  have heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  exact groupMemberSourceWithWork_value scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j))

end BinaryFraction
end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryGradientWork

namespace OAI

/-! Group evaluation reads the exact finite sampler indexed by the count
computed from the stored rational scale. Casting indices below is proof
transport only; the emitted natural count is used by the executed loop. -/

namespace EditApproximation
namespace BinaryFraction

def countedGroupMemberWithWork {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) : BinaryFraction × ℕ :=
  let counts := vectorMapWithWork T fun t => groupSampleCountWithWork M Q b (scales t)
  let count := fun t => bitWordValue (counts.1.get t)
  let heq : ∀ t, count t = groupSampleCount M Q b (scales t).value := by
    intro t
    simp only [count, counts, vectorMapWithWork_value, groupSampleCountWithWork_value]
  let result := groupMemberWithWork scales count connection envelope values
    (fun t j => draw t (Fin.cast (heq t) j))
  (result.1, counts.2 + result.2 + 1)

theorem groupMemberWithWork_transport {M T : ℕ}
    (scales : Fin T → BinaryFraction) (left right : Fin T → ℕ) (h : ∀ t, left t = right t)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (right t) → Fin M) :
    groupMemberWithWork scales left connection envelope values (fun t j => draw t (Fin.cast (h t) j)) =
      groupMemberWithWork scales right connection envelope values draw := by
  have heq : left = right := funext h
  subst right
  rfl

@[simp] theorem countedGroupMemberWithWork_value {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M) :
    (countedGroupMemberWithWork Q b scales connection envelope values draw).1.value =
      groupMemberEstimate (fun t => (scales t).value) (fun t => groupSampleCount M Q b (scales t).value)
        connection.value (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  unfold countedGroupMemberWithWork
  dsimp only
  rw [groupMemberWithWork_transport]
  exact groupMemberWithWork_value _ _ _ _ _ _

theorem countedGroupMemberWithWork_cost {M T : ℕ} (Q b : ℕ) (scales : Fin T → BinaryFraction)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (B C W : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hs : ∀ t, (scales t).width ≤ B)
    (hconn : connection.width ≤ B)
    (hc : ∀ t, (groupScaleWithWork (groupSampleCount M Q b (scales t).value) (scales t)
      envelope values (draw t)).2 ≤ C)
    (hw : ∀ t, (groupScaleWithWork (groupSampleCount M Q b (scales t).value) (scales t)
      envelope values (draw t)).1.width ≤ W) :
    (countedGroupMemberWithWork Q b scales connection envelope values draw).2 ≤
      T * (groupSampleCountBitBudget B + 6) + groupMemberBitBudget T B C W + 1 := by
  have hcounts := vectorMapWithWork_cost_le T (fun t => groupSampleCountWithWork M Q b (scales t))
    (groupSampleCountBitBudget B) (fun t => (groupSampleCountWithWork_bounds M Q b (scales t) B hM hQ hb (hs t)).2)
  have hmember := (groupMemberWithWork_bounds scales
    (fun t => groupSampleCount M Q b (scales t).value) connection envelope values draw B C W hconn hc hw).2
  unfold countedGroupMemberWithWork
  dsimp only
  rw [groupMemberWithWork_transport]
  omega

end BinaryFraction
end EditApproximation

end OAI

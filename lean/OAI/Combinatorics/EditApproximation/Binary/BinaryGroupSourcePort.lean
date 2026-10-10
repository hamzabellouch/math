import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedGroup
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact finite-count source reads inside a sampled group estimator.
A source read is executed only in the sampled branch; an exact scale
uses the complete child array and makes no random-source lookup. -/

namespace EditApproximation.BinaryFraction

/-- The exact number of source calls at one group scale. -/
def groupScaleSourceCalls (M k : ℕ) : ℕ := if k = M then 0 else k



theorem groupScaleSourceWithWork_value {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ) :
    (groupScaleSourceWithWork k h envelope values draw).1 =
      (groupScaleWithWork k h envelope values (fun i => (draw i).1)).1 := by
  unfold groupScaleSourceWithWork groupScaleWithWork
  split_ifs <;> simp only [arithmeticMapWithWork_value]

theorem groupScaleSourceCalls_le_work {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    groupScaleSourceCalls M k ≤ (groupScaleWithWork k h envelope values draw).2 := by
  unfold groupScaleSourceCalls
  split_ifs with heq
  · exact Nat.zero_le _
  · have hl := arithmeticMapWithWork_length_le_cost
      (fun i : Fin M => let test := equalWithWork (envelope.get i) h
        (if test.1 then values.get i else zero, test.2 + 2)) ((List.finRange k).map draw)
    simp only [List.length_map, List.length_finRange] at hl
    change k ≤ (groupTermsWithWork h envelope values ((List.finRange k).map draw)).2 at hl
    unfold groupScaleWithWork
    rw [ite_eq_right heq]
    unfold groupIndexWithWork
    dsimp only
    omega

theorem groupScaleSourceWithWork_cost {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M × ℕ)
    (R : ℕ) (hr : ∀ i, (draw i).2 ≤ R) :
    (groupScaleSourceWithWork k h envelope values draw).2 ≤
      (groupScaleWithWork k h envelope values (fun i => (draw i).1)).2 * (R + 4) := by
  have hmap := arithmeticMapWithWork_cost draw (List.finRange k) R (fun i _ => hr i)
  simp only [List.length_finRange] at hmap
  have hcalls := groupScaleSourceCalls_le_work k h envelope values (fun i => (draw i).1)
  by_cases heq : k = M
  · unfold groupScaleSourceWithWork groupScaleWithWork
    simp only [heq, ite_true, Nat.zero_add]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · unfold groupScaleSourceWithWork
    rw [ite_eq_right heq]
    dsimp only
    rw [arithmeticMapWithWork_value]
    unfold groupScaleWithWork at hcalls ⊢
    rw [ite_eq_right heq] at hcalls ⊢
    unfold groupScaleSourceCalls at hcalls
    rw [ite_eq_right heq] at hcalls
    simp only [ite_eq_right heq] at hcalls ⊢
    nlinarith only [hmap, hcalls]

end EditApproximation.BinaryFraction

end OAI

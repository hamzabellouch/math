import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Representative scores use literal reader calls at their child
coordinates. The stored value agrees with the previous arithmetic kernel. -/

namespace EditApproximation
namespace BinaryFraction



theorem endpointScoreReadWithWork_eq {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n) :
    (endpointScoreReadWithWork r read states).1 =
      (endpointScoreWithWork r (fun i q => (read i q).1) states).1 := by
  simp only [endpointScoreReadWithWork, endpointScoreWithWork,
    arithmeticMapWithWork_value, List.ofFn_eq_map]

theorem endpointScoreReadWithWork_cost {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 + M * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun i => read i (states i))
    (List.finRange M) R (fun i _ => hr i)
  simp only [List.length_finRange] at h
  simp only [endpointScoreReadWithWork, endpointScoreWithWork,
    arithmeticMapWithWork_value, List.ofFn_eq_map]
  omega



theorem wideMinimumReadWithWork_eq {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) :
    (wideMinimumReadWithWork r read actions hne).1 =
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1 := by
  simp only [wideMinimumReadWithWork, wideMinimumWithWork, arithmeticMapWithWork_value,
    endpointScoreReadWithWork_eq]

theorem wideMinimumReadWithWork_cost {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ []) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 +
        (actions.length + 1) * (M * (R + 3)) := by
  have h := arithmeticMapWithWork_extra (endpointScoreReadWithWork r read)
    (endpointScoreWithWork r (fun i q => (read i q).1)) (fun _ => M * (R + 3)) actions
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_cost r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_cost r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hs : (actions.map (fun _ => M * (R + 3))).sum = actions.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold wideMinimumReadWithWork wideMinimumWithWork
  dsimp only
  rw [endpointScoreReadWithWork_eq, h.1]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end BinaryFraction
end EditApproximation

end OAI

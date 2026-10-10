import OAI.Combinatorics.EditApproximation.Queries.QueryInputCodes
import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentatives
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The earlier-history cover is materialized from its small coordinate
lists, then sorted by the original history encoding. It never enumerates
the much larger Cartesian set of complete wide actions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawHistoryInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P history : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1 =
      representatives.flatMap (fun br => (List.finRange M).flatMap fun i =>
        (List.range history).flatMap fun t =>
          (wideChildStateList parent br.2 br.1 P i).map fun r => (i, t, r)) := by
  simp only [queryRawHistoryInputsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, wideChildGridWithWork_value _ _ _ _ _ hP]

theorem queryRawHistoryInputsWithWork_cover {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P history : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.toFinset =
      wideEarlierInputCover parent P history representatives := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_range, List.mem_map, wideEarlierInputCover, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_range, Finset.mem_image]



theorem queryEarlierInputsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1 =
      orderedInputs historyInputCode (historyInputCode_injective M ny)
        (queryEarlierInputCover parent N P F exponent history a.value
          (fun r => (initial r).1.value) q) := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value,
    queryRawHistoryInputsWithWork_cover _ _ _ _ hP,
    queryEarlierRepresentativesWithWork_value _ _ _ _ hP _ _ _ R hR, queryEarlierInputCover]

end BinaryFraction
end EditApproximation

end OAI

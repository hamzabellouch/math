import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSamples
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedGeometry
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A shared estimator requests every child when its exact sample count
equals the arity; otherwise it requests the sampled child labels. The
Boolean test and each draw-table lookup are included in the counter. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryGroupLabelsWithWork_value (M Q b : ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ) :
    (queryGroupLabelsWithWork M Q b h draw).1.toFinset =
      groupQueriedChildLabels M Q b h.value (fun i => (draw i).1) := by
  have ht : (naturalEqualWithWork (bitWordValue (groupSampleCountWithWork M Q b h).1) M).1 = true ↔
      groupSampleCount M Q b h.value = M := by
    rw [naturalEqualWithWork_value, groupSampleCountWithWork_value]
  unfold queryGroupLabelsWithWork groupQueriedChildLabels
  by_cases he : groupSampleCount M Q b h.value = M
  · rw [ite_eq_left (ht.mpr he), ite_eq_left he]
    ext i
    simp
  · rw [ite_eq_right (fun hx => he (ht.mp hx)), ite_eq_right he]
    simp only [arithmeticMapWithWork_value]
    ext i
    simp



theorem queryGroupInputsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent Q : ℕ) (cell : ℕ × ℕ)
    (h : BinaryFraction) (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ) :
    (queryGroupInputsWithWork (ny := target.length) parent b exponent Q cell h draw).1.toFinset =
      groupCurrentInputCover source target parent b exponent Q cell h.value (fun i => (draw i).1) := by
  have hl := queryGroupLabelsWithWork_value M Q b h draw
  simp only [queryGroupInputsWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, queryGroupRoundedStatesWithWork_value source target]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, groupCurrentInputCover,
    Finset.mem_biUnion, Finset.mem_image]
  simp only [← hl, List.mem_toFinset]

end BinaryFraction
end EditApproximation

end OAI

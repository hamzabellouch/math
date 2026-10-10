import OAI.Combinatorics.EditApproximation.Queries.QueryGroupInputs
import OAI.Combinatorics.EditApproximation.Queries.QueryInputCodes
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The shared-current request list is built from counted whole-cell
enumerations and sorted by the original child encoding. -/

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupInputsTransportWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b exponent Q : ℕ) (cell : ℕ × ℕ)
    (word : BinaryFraction) (scale : ℚ) (hv : word.value = scale)
    (draw : Fin (groupSampleCount M Q b scale) → Fin M × ℕ) :
    (queryGroupInputsTransportWithWork (ny := target.length) parent b exponent Q cell word scale hv draw).1.toFinset =
      groupCurrentInputCover source target parent b exponent Q cell scale (fun i => (draw i).1) := by
  subst scale
  exact queryGroupInputsWithWork_value source target parent b exponent Q cell word draw



theorem querySharedCellInputsWithWork_value {α : Type*} (source target : List α)
    (M F Q eM eb eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (parent : TargetInterval source.length) (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ) :
    (querySharedCellInputsWithWork (ny := target.length) M F Q eM eb eF hM hF parent exponent cell draw).1.toFinset =
      Finset.univ.biUnion (fun scale => groupCurrentInputCover source target parent (2 ^ eb) exponent Q cell
        (groupDyadicScaleAt M (2 ^ eb) F scale) (fun sample => (draw scale sample).1)) := by
  simp only [querySharedCellInputsWithWork, arithmeticFlatMapWithWork_value, queryFinRange_value]
  ext input
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
    Finset.mem_biUnion, Finset.mem_univ]
  apply exists_congr
  intro scale
  rw [← List.mem_toFinset, queryGroupInputsTransportWithWork_value source target]



theorem querySharedInputsWithWork_value {α : Type*} (source target : List α)
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (parent : TargetInterval source.length) (a value : BinaryFraction)
    (query : TargetInterval target.length) (draw : CountedCellGroupDraws M F Q) :
    (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a value query draw).1 =
      orderedInputs childInputCode (childInputCode_injective M target.length)
        (querySharedInputCover source target parent N F exponent Q a.value (fun _ => value.value) query
          (fun b cell scale sample => (draw b cell scale sample).1)) := by
  have hc (e : ℕ) (cell : ℕ × ℕ) (input : Fin M × TargetInterval target.length) :
      input ∈ (querySharedCellInputsWithWork (ny := target.length) M F Q eM e eF hM hF parent
        exponent cell (draw (2 ^ e) cell)).1 ↔
      ∃ scale, input ∈ groupCurrentInputCover source target parent (2 ^ e) exponent Q cell
        (groupDyadicScaleAt M (2 ^ e) F scale) (fun sample => (draw (2 ^ e) cell scale sample).1) := by
    rw [← List.mem_toFinset, querySharedCellInputsWithWork_value source target]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  simp only [querySharedInputsWithWork, queryOrderedChildInputsWithWork_value]
  apply congrArg (orderedInputs childInputCode (childInputCode_injective M target.length))
  unfold querySharedInputCover localGroupQueryKeys
  rw [← queryExponentsWithWork_value N F a value]
  ext input
  simp only [arithmeticFlatMapWithWork_value, targetCellsWithWork_value,
    canonicalMulWithWork_value, inversePowerTwo_value, nat_value, naturalCeilingWithWork_value,
    List.mem_toFinset, List.mem_flatMap, List.flatMap_map, List.mem_map, Finset.mem_biUnion,
    Finset.mem_univ, true_and, hc]
  aesop

end BinaryFraction
end EditApproximation

end OAI

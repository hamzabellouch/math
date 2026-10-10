import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSetupSpace
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputs
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupInputsTransportAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (word : BinaryFraction) (scale : ℚ)
    (hv : word.value = scale) (draw : Fin (groupSampleCount M Q b scale) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b scale) → ℕ)
    (ha : ∀ sample, allocation sample ≤ (draw sample).2) :
    queryGroupInputsTransportAllocation (ny := ny) parent b exponent Q cell word scale hv draw allocation ≤
      (queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word scale hv draw).2 :=
  queryGroupInputsAllocation_le_work _ _ _ _ _ _ _ _ (fun _ => ha _)



theorem querySharedCellInputsAllocation_le_work {nx ny : ℕ} (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : TargetInterval nx)
    (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ)
    (allocation : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → ℕ)
    (ha : ∀ scale sample, allocation scale sample ≤ (draw scale sample).2) :
    querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell draw allocation ≤
      (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell draw).2 := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hM rfl hF
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  let indices := queryFinRange scales.1.length (groupDyadicScales M b F).length hlen
  let build := fun scale =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let hv : word.value = groupDyadicScaleAt M b F scale := queryGroupScaleAt_value M b F _ hs scale
    let states := queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word
      (groupDyadicScaleAt M b F scale) hv (draw scale)
    (states.1, states.2 + scales.1.length + 1)
  let alloc := fun scale =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let hv : word.value = groupDyadicScaleAt M b F scale := queryGroupScaleAt_value M b F _ hs scale
    queryGroupInputsTransportAllocation (ny := ny) parent b exponent Q cell word
      (groupDyadicScaleAt M b F scale) hv (draw scale) (allocation scale)
  have hg := groupScalesAllocation_le_work eM eb eF
  have hi := arithmeticFlatMapAllocation_le_work build alloc indices (by
    intro scale _
    have hh := queryGroupInputsTransportAllocation_le_work (ny := ny) parent b exponent Q cell
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale) (groupDyadicScaleAt M b F scale)
      (queryGroupScaleAt_value M b F _ hs scale) (draw scale) (allocation scale) (ha scale)
    dsimp only [alloc, build]
    omega)
  unfold querySharedCellInputsAllocation querySharedCellInputsWithWork
  dsimp only [build, alloc, b, scales, indices] at hi ⊢
  omega



theorem querySharedInputsAllocation_le_work {nx ny : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : TargetInterval nx)
    (a value : BinaryFraction) (query : TargetInterval ny) (draw : CountedCellGroupDraws M F Q)
    (allocation : CountedCellGroupAllocations M F Q)
    (ha : ∀ b cell scale sample, allocation b cell scale sample ≤ (draw b cell scale sample).2) :
    querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a value query draw allocation ≤
      (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a value query draw).2 := by
  let scales := (queryExponentsWithWork N F a value).1
  let radius := (naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    let cells := targetCellsWithWork side.1 (bitWordValue radius) query
    let states := arithmeticFlatMapWithWork (fun cell =>
      querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell)) cells.1
    (states.1, side.2 + cells.2 + states.2 + eb + exponent + 4)
  let alloc := fun eb =>
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    let cells := (targetCellsWithWork side (bitWordValue radius) query).1
    canonicalMulAllocation (inversePowerTwo exponent) (nat (2 ^ eb)) + targetCellsAllocation side (bitWordValue radius) query +
      arithmeticFlatMapAllocation
        (fun cell => querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell))
        (fun cell => querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell
          (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell)) cells + eb + exponent + 2
  have he := queryExponentsAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hi := arithmeticFlatMapAllocation_le_work build alloc scales (by
    intro eb _
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    have hs := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat (2 ^ eb))
    have hc := targetCellsAllocation_le_work side (bitWordValue radius) query
    have hm := arithmeticFlatMapAllocation_le_work
      (fun cell => querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell))
      (fun cell => querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell
        (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell)) (targetCellsWithWork side (bitWordValue radius) query).1
      (fun cell _ => querySharedCellInputsAllocation_le_work (ny := ny) M F Q eM eb eF hM hF parent exponent cell
        (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell) (ha (2 ^ eb) cell))
    dsimp only [build, alloc, side] at hc hm ⊢
    omega)
  have ho := queryOrderedChildInputsAllocation_le_work (arithmeticFlatMapWithWork build scales).1
  unfold querySharedInputsAllocation querySharedInputsWithWork
  dsimp only [build, alloc, scales, radius] at hi ho ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI

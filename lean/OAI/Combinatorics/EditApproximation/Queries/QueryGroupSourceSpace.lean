import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSetupSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSources
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction





theorem groupKeySampleBlockAllocation_le_work {M F Q : ℕ} (b : ℕ) (raw : List BinaryFraction)
    (hs : raw.map value = groupDyadicScales M b F) (cell : ℕ × ℕ)
    (scale : Fin (groupDyadicScales M b F).length) :
    groupKeySampleBlockAllocation (Q := Q) b raw hs cell scale ≤ (groupKeySampleBlock (Q := Q) b raw hs cell scale).2 := by
  let word := queryScaleAt raw (groupDyadicScales M b F) hs scale
  let count := groupSampleCountWithWork M Q b word
  have hc : bitWordValue count.1 = groupSampleCount M Q b (groupDyadicScaleAt M b F scale) := by
    rw [groupSampleCountWithWork_value, queryScaleAt_value]
    rfl
  let coordinates := queryFinRange (bitWordValue count.1)
    (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) hc
  have hg := groupSampleCountAllocation_le_work M Q b word
  have hm := arithmeticMapAllocation_with_spine (fun sample =>
    ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2)) (fun _ => 2) coordinates (fun _ _ => le_rfl)
  unfold groupKeySampleBlockAllocation groupKeySampleBlock
  dsimp only [word, count, coordinates] at hg hm ⊢
  omega



theorem queryGroupKeySamplesAllocation_le_work (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    queryGroupKeySamplesAllocation M F Q eM eb eF hM hF cell ≤
      (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF cell).2 := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hM rfl hF
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  have hg := groupScalesAllocation_le_work eM eb eF
  have hm := arithmeticFlatMapAllocation_le_work (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
    (groupKeySampleBlockAllocation (Q := Q) b scales.1 hs cell)
    (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen)
    (fun scale _ => groupKeySampleBlockAllocation_le_work (Q := Q) b scales.1 hs cell scale)
  change groupScalesAllocation eM eb eF + 2 * scales.1.length + eb + 1 +
    arithmeticFlatMapAllocation (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
      (groupKeySampleBlockAllocation (Q := Q) b scales.1 hs cell)
      (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen) ≤
    scales.2 + 4 * scales.1.length +
      (arithmeticFlatMapWithWork (groupKeySampleBlock (Q := Q) b scales.1 hs cell)
        (queryFinRange scales.1.length (groupDyadicScales M b F).length hlen)).2 + eb + 4
  change groupScalesAllocation eM eb eF ≤ scales.2 at hg
  omega



theorem queryGroupSourceKeysAllocation_le_work {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n) :
    queryGroupSourceKeysAllocation M N F Q exponent eM eF hM hF a value q ≤
      (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))
    let cells := targetCellsWithWork side.1 (bitWordValue radius) q
    let sources := arithmeticFlatMapWithWork (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF) cells.1
    (sources.1, side.2 + cells.2 + sources.2 + eb + exponent + 4)
  let allocation := fun eb =>
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    let cells := (targetCellsWithWork side (bitWordValue radius) q).1
    canonicalMulAllocation (inversePowerTwo exponent) (nat (2 ^ eb)) + targetCellsAllocation side (bitWordValue radius) q +
      arithmeticFlatMapAllocation (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF)
        (queryGroupKeySamplesAllocation M F Q eM eb eF hM hF) cells + eb + exponent + 2
  have he := queryExponentsAllocation_le_work N F a value
  have hr := naturalCeilingAllocation_le_work value
  have hg := arithmeticFlatMapAllocation_le_work build allocation (queryExponentsWithWork N F a value).1 (by
    intro eb _
    let side := (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
    have hs := canonicalMulAllocation_le_work (inversePowerTwo exponent) (nat (2 ^ eb))
    have hc := targetCellsAllocation_le_work side (bitWordValue radius) q
    have hm := arithmeticFlatMapAllocation_le_work (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF)
        (queryGroupKeySamplesAllocation M F Q eM eb eF hM hF)
        (targetCellsWithWork side (bitWordValue radius) q).1
        (fun cell _ => queryGroupKeySamplesAllocation_le_work M F Q eM eb eF hM hF cell)
    dsimp only [build, allocation, side] at hc hm ⊢
    omega)
  unfold queryGroupSourceKeysAllocation queryGroupSourceKeysWithWork
  dsimp only [build, allocation, radius] at hg ⊢
  omega

end EditApproximation.BinaryFraction

end OAI

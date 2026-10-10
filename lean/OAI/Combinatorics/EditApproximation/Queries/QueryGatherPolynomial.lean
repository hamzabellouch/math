import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgramCost
import OAI.Combinatorics.EditApproximation.Geometry.PreparedKernelPolynomial

namespace OAI

/-! A finite polynomial certificate for the complete adaptive gather cost.
The four kernel bounds and the two Cartesian counts
are explicit inputs. Every remaining operation is addition, multiplication,
fixed natural power, or bit length. -/

namespace EditApproximation

private abbrev GP := FiniteBitPolynomial (Fin 16)

private def gp_localEligibilityBitBudget (B : GP) : GP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8

private def gp_queryExponentsBitBudget (B : GP) : GP :=
  (B + 1) * (gp_localEligibilityBitBudget (B + 4) + B + 5) + 2 * B + 3

private def gp_queryScalesBitBudget (B : GP) : GP :=
  gp_queryExponentsBitBudget B + (B + 1) * (B + 6) + 1

private def gp_gridPointsBitBudget (n B : GP) : GP :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)

private def gp_gridStateBoxBitBudget (count B : GP) : GP :=
  96 * (B + 1) + 2 * gp_gridPointsBitBudget count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6

private def gp_queryGridPointsBitBudget (P K B : GP) : GP :=
  100 * (B + 2) ^ 2 + gp_gridStateBoxBitBudget (4 * K * P + 2) (B + 1) + 1

private def gp_queryRawCentersBitBudget (P F B : GP) : GP :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  gp_queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_queryGridPointsBitBudget P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

private def gp_cellCoordinateSetupBitBudget (B : GP) : GP :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)

private def gp_targetCellsBitBudget (left right B : GP) : GP :=
  2 * gp_cellCoordinateSetupBitBudget B + left + right + left * (5 * right + 3) + 2

private def gp_queryCellScanBitBudget (aux : Fin 7 → GP) (F _exponent B : GP) : GP :=
  let K := (32 * F + 2) * (aux 0) + 2
  2000 * (B + 4) ^ 2 + gp_targetCellsBitBudget K K (4 * B + 40)

private def gp_queryGroupKeysBitBudget (aux : Fin 7 → GP) (F exponent B : GP) : GP :=
  let L := ((32 * F + 2) * (aux 0) + 2) ^ 2
  gp_queryScalesBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * ((gp_queryCellScanBitBudget aux) F exponent B + 5 * L + 5) + exponent + 4

private def gp_cellGridSetupBitBudget (B : GP) : GP :=
  2000000 * (B + 100) ^ 2

private def gp_cellGridPointBitBudget (B : GP) : GP :=
  1000 * (B + 100) ^ 2

private def gp_cellGridPointsBitBudget (count B : GP) : GP :=
  gp_cellGridSetupBitBudget B + count * (gp_cellGridPointBitBudget B + 5)

private def gp_cellStatesBitBudget (left right B : GP) : GP :=
  gp_cellGridPointsBitBudget left B + gp_cellGridPointsBitBudget right B +
    left * (right * (16 * (17 * B + 78) + 11) + right + 3) + 2

private def gp_queryCellStatesBitBudget (P exponent B : GP) : GP :=
  100 * (B + 5) ^ 2 + 2000 * (B + 4) ^ 2 +
    gp_cellStatesBitBudget P P (16 * B + 200) + exponent + 3

private def gp_queryOnlineKeysBitBudget (B : GP) : GP :=
  gp_queryScalesBitBudget B + (B + 1) * (600 * (B + 3) ^ 2 + 6) + 1

private def gp_queryInitialSupportBitBudget (aux : Fin 7 → GP) (P F exponent B : GP) : GP :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  gp_queryRawCentersBitBudget P F B + (gp_queryGroupKeysBitBudget aux) F exponent B +
    groups * (gp_queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
    gp_queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * raw + groups * P ^ 2 + 5

private def gp_queryInitialSupportLength (aux : Fin 7 → GP) (P F _exponent B : GP) : GP :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  1 + raw + groups * P ^ 2 + (B + 1)

private def gp_queryInitialGatherBitBudget (aux : Fin 7 → GP) (P F exponent B R K : GP) : GP :=
  R + (gp_queryInitialSupportBitBudget aux) P F exponent B + (gp_queryInitialSupportLength aux) P F exponent B * (R + 3) + K

private def gp_localRepresentativeScaleBitBudget (P F B : GP) : GP :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gp_gridStateBoxBitBudget L C +
    L ^ 2 * (gp_localEligibilityBitBudget C + 3) + L ^ 2 * 4 + B + 6

private def gp_localRepresentativesBitBudget (P F B : GP) : GP :=
  gp_queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_localRepresentativeScaleBitBudget P F B + (64 * F * P + 2) ^ 2 + 3) + 3

private def gp_cellCentersBitBudget (left right B : GP) : GP :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    gp_cellStatesBitBudget left right (4 * B + 40) +
    left * right * (gp_localEligibilityBitBudget B + 3) + 3

private def gp_queryEarlierRepresentativesBitBudget (aux : Fin 7 → GP) (P F exponent B R : GP) : GP :=
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  let L := (P + 1) ^ 2
  R + gp_localRepresentativesBitBudget P F B * (R + 2) + (gp_queryGroupKeysBitBudget aux) F exponent B +
    groups * (gp_cellCentersBitBudget P P (16 * B + 200) * (R + 1) + 5 * L + 4) +
    gp_queryOnlineKeysBitBudget B + 2 * ((B + 1) * (64 * F * P + 2) ^ 2) + groups * L + 4

private def gp_wideChildGridBitBudget (P B : GP) : GP :=
  10000 * (B + 12) ^ 2 + gp_gridStateBoxBitBudget (40 * P + 2) (B + 12)

private def gp_queryWideInputsBitBudget (M P count B : GP) : GP :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

private def gp_queryEarlierRepresentativesLength (aux : Fin 7 → GP) (P F _exponent B : GP) : GP :=
  (B + 1) * ((64 * F * P + 2) ^ 2 +
    ((32 * F + 2) * (aux 0) + 2) ^ 2 * (P + 1) ^ 2 + 1)

private def gp_queryBandInputsBitBudget (aux : Fin 7 → GP) (M P F exponent B R : GP) : GP :=
  (gp_queryEarlierRepresentativesBitBudget aux) P F exponent B R +
    gp_queryWideInputsBitBudget M P ((gp_queryEarlierRepresentativesLength aux) P F exponent B) B + 1

private def gp_queryBandGatherBitBudget (aux : Fin 7 → GP) (M P F exponent B Rp W K : GP) : GP :=
  (gp_queryBandInputsBitBudget aux) M P F exponent B Rp +
    2 * ((gp_queryEarlierRepresentativesLength aux) P F exponent B * (M * (40 * P + 2) ^ 2) * (W + 3)) + K

private def gp_groupScalesBitBudget (eM eb eF : GP) : GP :=
  (7 + eM + eF) * (eM + eb + eF + 13) +
    FiniteBitPolynomial.bitLength eM + FiniteBitPolynomial.bitLength eb + FiniteBitPolynomial.bitLength eF + 8

private def gp_groupSampleCountBitBudget (B : GP) : GP :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 500 * (64 * B + 45) ^ 2 +
    4 * (65 * B + 46) + 3 * B + 8

private def gp_queryGroupSamplesBitBudget (M eM eb eF B : GP) : GP :=
  let L := 7 + eM + eF
  gp_groupScalesBitBudget eM eb eF + 4 * L +
    L * (L + gp_groupSampleCountBitBudget B + 7 * M + 6) + eb + 4

private def gp_queryGroupSourceKeysBitBudget (aux : Fin 7 → GP) (M F exponent eM eF B : GP) : GP :=
  let cells := ((32 * F + 2) * (aux 0) + 2) ^ 2
  let samples := (7 + eM + eF) * M
  let sampleWork := gp_queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let scaleWork := (gp_queryCellScanBitBudget aux) F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  gp_queryExponentsBitBudget B + 500 * (B + 1) ^ 2 +
    (B + 1) * (scaleWork + cells * samples + 3) + 2

private def gp_queryGroupSourceKeysLength (aux : Fin 7 → GP) (M F _exponent eM eF B : GP) : GP :=
  (B + 1) * ((((32 * F + 2) * (aux 0) + 2) ^ 2) * ((7 + eM + eF) * M))

private def gp_queryGroupGatherBitBudget (aux : Fin 7 → GP) (M F exponent eM eF B Rp W K : GP) : GP :=
  Rp + (gp_queryGroupSourceKeysBitBudget aux) M F exponent eM eF B +
    (gp_queryGroupSourceKeysLength aux) M F exponent eM eF B * (W + 3) + K

private def gp_wideMaterializationBitBudget (aux : Fin 7 → GP) (M P B : GP) : GP :=
  M * (gp_wideChildGridBitBudget P B + 6) +
    (M + 1) * (6 * M + 10) * (aux 2) + 1

private def gp_tableReadFactor (R : GP) : GP :=
  4 * (R + 4)

private def gp_bandCoordinatesBitBudget (M vertices B : GP) : GP :=
  vertices * (5 * M + 3) + (vertices * M + 1) ^ 2 * (24 * B + 12) + 1

private def gp_bitPowerBitBudget (n B : GP) : GP :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

private def gp_onlineIndexBitBudget (M vertices B : GP) : GP :=
  gp_bandCoordinatesBitBudget M vertices B + 40 * (B + 4) +
    gp_bitPowerBitBudget 80 (B + 4) + 3

private def gp_queryOnlineRangeBitBudget (aux : Fin 7 → GP) (M P B R : GP) : GP :=
  let V := (aux 1)
  26 * B + 4 +
    ((gp_wideMaterializationBitBudget aux) M P B + (aux 6) + V + 1) *
      gp_tableReadFactor R + gp_onlineIndexBitBudget M V B + gp_bitPowerBitBudget 80 (B + 4) +
      10000 * (80 * (B + 4) + 4) ^ 2 + 4

private def gp_queryOnlineGatherBitBudget (aux : Fin 7 → GP) (M P B Rp R W K : GP) : GP :=
  Rp + gp_queryOnlineKeysBitBudget B +
    (B + 1) * ((gp_queryOnlineRangeBitBudget aux) M P (B + 1) R + W + 3) + K

private def gp_queryHistoryInputsLength (M P history count : GP) : GP :=
  count * (M * (history * (40 * P + 2) ^ 2))

private def gp_queryGroupInputsLength (aux : Fin 7 → GP) (M _exponent : GP) : GP :=
  M * ((24 * (aux 0) * M + 2) * (4 * (aux 0) + 4))

private def gp_querySharedCellInputsLength (aux : Fin 7 → GP) (M exponent eM eF : GP) : GP :=
  (7 + eM + eF) * (gp_queryGroupInputsLength aux) M exponent

private def gp_querySharedInputsLength (aux : Fin 7 → GP) (M F exponent eM eF B : GP) : GP :=
  (B + 1) * ((((32 * F + 2) * (aux 0) + 2) ^ 2) * (gp_querySharedCellInputsLength aux) M exponent eM eF)

private def gp_queryRefinementReadBudget (B Rp R earlier shared : GP) : GP :=
  R + Rp + (1 + earlier * (32 * B + 12)) + (1 + shared * (24 * B + 9))

private def gp_queryNeededInputsBitBudget (actions M B : GP) : GP :=
  actions * (5 * M + 3) + 2 * M + actions * M +
    (actions * M + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 4

private def gp_queryRefinementStagesBudget (M B readCost earlierLength earlierCost onlineLength onlineCost sharedLength sharedCost groupLength groupCost parentCost finishCost : GP) : GP :=
  earlierCost + earlierLength * (readCost + 3) + onlineCost + parentCost + sharedCost +
    sharedLength * (readCost + 3) + groupCost +
    gp_queryNeededInputsBitBudget (groupLength + onlineLength) M B +
    (groupLength + onlineLength) * M * (readCost + 3) + finishCost

private def gp_queryRawHistoryInputsBitBudget (M P history count B : GP) : GP :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget P (B + 1)
  count * (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
    M * (history * G) + 3) + M + 1

private def gp_queryEarlierInputsBitBudget (aux : Fin 7 → GP) (M P F exponent history B R : GP) : GP :=
  let count := (gp_queryEarlierRepresentativesLength aux) P F exponent B
  (gp_queryEarlierRepresentativesBitBudget aux) P F exponent B R +
    gp_queryRawHistoryInputsBitBudget M P history count B +
    (gp_queryHistoryInputsLength M P history count + 1) ^ 2 * (2002000 * (B + 1) ^ 2) + 2

private def gp_groupSampleCountWordBudget (B : GP) : GP :=
  64 * B + 46

private def gp_queryGroupLabelsBitBudget (M B R : GP) : GP :=
  gp_groupSampleCountBitBudget B + 8 * (gp_groupSampleCountWordBudget B) +
    M * (R + 4) + 4

private def gp_queryGapStatesBitBudget (left right B : GP) : GP :=
  let C := 1000 * (B + 10) ^ 2
  C + gp_gridPointsBitBudget left (B + 2) +
    left * (C + gp_gridPointsBitBudget right (B + 6) + right * (16 * (B + 6) + 11) + right + 7) + 3

private def gp_queryRoundedStatesBitBudget (left right exponent B : GP) : GP :=
  100000 * (32 * B + 210) ^ 2 + gp_queryGapStatesBitBudget left right (32 * B + 200) + exponent + 12

private def gp_queryGroupInputsBitBudget (aux : Fin 7 → GP) (M exponent B R : GP) : GP :=
  let L := (24 * (aux 0) * M + 2) * (4 * (aux 0) + 4)
  gp_queryGroupLabelsBitBudget M B R +
    M * (gp_queryRoundedStatesBitBudget (24 * (aux 0) * M + 2) (4 * (aux 0) + 4) exponent B +
      5 * L + 4) + 1

private def gp_querySharedCellInputsBitBudget (aux : Fin 7 → GP) (M exponent eM eb eF B R : GP) : GP :=
  let L := 7 + eM + eF
  gp_groupScalesBitBudget eM eb eF + 4 * L +
    L * ((gp_queryGroupInputsBitBudget aux) M exponent B R + L + (gp_queryGroupInputsLength aux) M exponent + 4) + eb + 4

private def gp_querySharedInputsBitBudget (aux : Fin 7 → GP) (M F exponent eM eF B R : GP) : GP :=
  let cells := ((32 * F + 2) * (aux 0) + 2) ^ 2
  let samples := (gp_querySharedCellInputsLength aux) M exponent eM eF
  let sampleWork := (gp_querySharedCellInputsBitBudget aux) M exponent eM B eF (16 * B + 200) R
  let scaleWork := (gp_queryCellScanBitBudget aux) F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  gp_queryExponentsBitBudget B + 500 * (B + 1) ^ 2 + (B + 1) * (scaleWork + cells * samples + 3) +
    ((gp_querySharedInputsLength aux) M F exponent eM eF B + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 3

private def gp_queryRefinementFinishBitBudget (aux : Fin 7 → GP) (_M P F B R _G _O : GP) : GP :=
  R + gp_localRepresentativesBitBudget P F B * (R + 2) +
    (aux 5) * gp_tableReadFactor R + 2

private def gp_queryFinishReadBudget (M B Rp earlierCount groups online : GP) : GP :=
  Rp + 2 + earlierCount * (32 * B + 12) + (groups + online) * M * (24 * B + 9)

private def gp_queryLocalRefinementBitBudget (aux : Fin 7 → GP) (M _N P F exponent eM eF B _S t Rp R W Dg Do : GP) : GP :=
  let earlier := gp_queryHistoryInputsLength M P t ((gp_queryEarlierRepresentativesLength aux) P F exponent B)
  let shared := (gp_querySharedInputsLength aux) M F exponent eM eF B
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  let U := gp_queryRefinementReadBudget B Rp R earlier shared
  gp_queryRefinementStagesBudget M B W earlier ((gp_queryEarlierInputsBitBudget aux) M P F exponent t B Rp)
    (B + 1) ((aux 4) * gp_tableReadFactor U * (Do + 4))
    shared ((gp_querySharedInputsBitBudget aux) M F exponent eM eF B Dg)
    groups ((aux 3) * gp_tableReadFactor U * (Dg + 4)) Rp
    ((gp_queryRefinementFinishBitBudget aux) M P F B (gp_queryFinishReadBudget M B Rp earlier groups (B + 1)) groups (B + 1))

private def gp_queryGroupBufferReadBudget (count B V : GP) : GP :=
  count * (40 * (40 * B + 500) + 15) + 200 * (V + 1) ^ 2 +
    30 * (V + 1) * (V + (40 * B + 500) + 1) + 4

private def gp_queryBufferedGroupReadBudget (aux : Fin 7 → GP) (M F exponent eM eF B V : GP) : GP :=
  gp_queryGroupBufferReadBudget ((gp_queryGroupSourceKeysLength aux) M F exponent eM eF B) B V

private def gp_queryOnlineBufferReadBudget (count B V : GP) : GP :=
  count * (24 * (B + 1) + 9) + 200 * (V + 1) ^ 2 + 2

private def gp_queryLocalSourcesBitBudget (aux : Fin 7 → GP) (M N P F exponent eM eF B S t Rp R W : GP) : GP :=
  (gp_queryGroupGatherBitBudget aux) M F exponent eM eF B Rp W
    ((gp_queryOnlineGatherBitBudget aux) M P B Rp R W
      ((gp_queryLocalRefinementBitBudget aux) M N P F exponent eM eF B S t Rp R W
        ((gp_queryBufferedGroupReadBudget aux) M F exponent eM eF B B)
        (gp_queryOnlineBufferReadBudget (B + 1) B B)))

private def gp_queryBandReadBudget (aux : Fin 7 → GP) (M P F exponent B : GP) : GP :=
  1 + (gp_queryEarlierRepresentativesLength aux) P F exponent B * (M * (40 * P + 2) ^ 2) * (24 * B + 9)

private def gp_queryLocalBandBitBudget (aux : Fin 7 → GP) (M N P F exponent eM eF B S t Rp W : GP) : GP :=
  (gp_queryBandGatherBitBudget aux) M P F exponent B Rp W
    ((gp_queryLocalSourcesBitBudget aux) M N P F exponent eM eF B S t Rp
      ((gp_queryBandReadBudget aux) M P F exponent B) W)

private def gp_queryParentBufferReadBudget (aux : Fin 7 → GP) (P F exponent B : GP) : GP :=
  1 + (gp_queryInitialSupportLength aux) P F exponent B * (16 * B + 6)

private def gp_queryLocalProgramBitBudget (aux : Fin 7 → GP) (M N P F exponent eM eF B S t W : GP) : GP :=
  (gp_queryInitialGatherBitBudget aux) P F exponent B W
    ((gp_queryLocalBandBitBudget aux) M N P F exponent eM eF B S t
      ((gp_queryParentBufferReadBudget aux) P F exponent B) W)

private def queryGatherPolynomial : GP :=
  let aux : Fin 7 → GP := ![.input 9, .input 10, .input 11, .input 12, .input 13, .input 14, .input 15]
  gp_queryLocalProgramBitBudget aux (.input 0) 0 (.input 1) (.input 2) (.input 3)
    (.input 4) (.input 5) (.input 6) 0 (.input 7) (.input 8)

def queryGatherBitDegree : ℕ := queryGatherPolynomial.degree

private def queryGatherEnvironment (M N P F exponent eM eF B S t W : ℕ) : Fin 16 → ℕ :=
  ![M, P, F, exponent, eM, eF, B, t, W, 2 ^ exponent,
    (40 * P + 2) ^ (2 * M), ((40 * P + 2) ^ 2 + 1) ^ (M + 1),
    BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B,
    BinaryFraction.preparedLocalOnlineBitBudget M P B S,
    BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
      ((B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2) (B + 1) (B + 4),
    BinaryFraction.representativeCompleteBitBudget M ((40 * P + 2) ^ (2 * M)) (4 * (B + 1) + 20)]

private theorem queryGatherPolynomial_eval (M N P F exponent eM eF B S t W : ℕ) :
    queryGatherPolynomial.eval (queryGatherEnvironment M N P F exponent eM eF B S t W) =
      BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W := by
  rfl

theorem queryLocalProgramBitBudget_fixedPower (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 2 ≤ X) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (he : exponent ≤ X)
    (heM : eM ≤ X) (heF : eF ≤ X) (hB : B ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hTheta : 2 ^ exponent ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hGroups : BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤ X)
    (hOnline : BinaryFraction.preparedLocalOnlineBitBudget M P B S ≤ X)
    (hFinish : BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
      ((B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2) (B + 1) (B + 4) ≤ X)
    (hRange : BinaryFraction.representativeCompleteBitBudget M ((40 * P + 2) ^ (2 * M))
      (4 * (B + 1) + 20) ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤ X ^ queryGatherBitDegree := by
  have henv : ∀ i, queryGatherEnvironment M N P F exponent eM eF B S t W i ≤ X := by
    intro i
    fin_cases i
    · exact hM
    · exact hP
    · exact hF
    · exact he
    · exact heM
    · exact heF
    · exact hB
    · exact ht
    · exact hW
    · exact hTheta
    · exact hV
    · exact hCart
    · exact hGroups
    · exact hOnline
    · exact hFinish
    · exact hRange
  simpa only [queryGatherPolynomial_eval, queryGatherBitDegree] using
    queryGatherPolynomial.eval_le_pow (queryGatherEnvironment M N P F exponent eM eF B S t W) X hX henv

end EditApproximation

end OAI

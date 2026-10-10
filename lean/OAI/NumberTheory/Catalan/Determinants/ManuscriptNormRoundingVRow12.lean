import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup052
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup053
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup054
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup055
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV12_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV12_0SubstituteRat_interval :
    manuscriptNormV12_0SubstituteRat ∈ Set.Icc manuscriptNormV12_0Interval.1 manuscriptNormV12_0Interval.2 := by
  simpa only [manuscriptNormV12_0SubstituteRat, manuscriptNormV12_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num))

private theorem manuscriptNormV12_0SubstituteRat_upper :
    manuscriptNormV12_0SubstituteRat ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) :=
  manuscriptNormV12_0SubstituteRat_interval.2.trans manuscriptNormV12_0_rounded_endpoints.2

def manuscriptNormV12_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV12_1SubstituteRat_interval :
    manuscriptNormV12_1SubstituteRat ∈ Set.Icc manuscriptNormV12_1Interval.1 manuscriptNormV12_1Interval.2 := by
  simpa only [manuscriptNormV12_1SubstituteRat, manuscriptNormV12_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num))

private theorem manuscriptNormV12_1SubstituteRat_upper :
    manuscriptNormV12_1SubstituteRat ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) :=
  manuscriptNormV12_1SubstituteRat_interval.2.trans manuscriptNormV12_1_rounded_endpoints.2

def manuscriptNormV12_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV12_2SubstituteRat_interval :
    manuscriptNormV12_2SubstituteRat ∈ Set.Icc manuscriptNormV12_2Interval.1 manuscriptNormV12_2Interval.2 := by
  simpa only [manuscriptNormV12_2SubstituteRat, manuscriptNormV12_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num))

private theorem manuscriptNormV12_2SubstituteRat_upper :
    manuscriptNormV12_2SubstituteRat ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) :=
  manuscriptNormV12_2SubstituteRat_interval.2.trans manuscriptNormV12_2_rounded_endpoints.2

def manuscriptNormV12_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV12_3SubstituteRat_interval :
    manuscriptNormV12_3SubstituteRat ∈ Set.Icc manuscriptNormV12_3Interval.1 manuscriptNormV12_3Interval.2 := by
  simpa only [manuscriptNormV12_3SubstituteRat, manuscriptNormV12_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num))

private theorem manuscriptNormV12_3SubstituteRat_upper :
    manuscriptNormV12_3SubstituteRat ≤ (418519297172338085081844233 / 100000000000000000000000000000) :=
  manuscriptNormV12_3SubstituteRat_interval.2.trans manuscriptNormV12_3_rounded_endpoints.2

def manuscriptNormV12_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV12_4SubstituteRat_interval :
    manuscriptNormV12_4SubstituteRat ∈ Set.Icc manuscriptNormV12_4Interval.1 manuscriptNormV12_4Interval.2 := by
  simpa only [manuscriptNormV12_4SubstituteRat, manuscriptNormV12_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num))

private theorem manuscriptNormV12_4SubstituteRat_upper :
    manuscriptNormV12_4SubstituteRat ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) :=
  manuscriptNormV12_4SubstituteRat_interval.2.trans manuscriptNormV12_4_rounded_endpoints.2

def manuscriptNormV12_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV12_5SubstituteRat_interval :
    manuscriptNormV12_5SubstituteRat ∈ Set.Icc manuscriptNormV12_5Interval.1 manuscriptNormV12_5Interval.2 := by
  simpa only [manuscriptNormV12_5SubstituteRat, manuscriptNormV12_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_5SubstituteRat_upper :
    manuscriptNormV12_5SubstituteRat ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) :=
  manuscriptNormV12_5SubstituteRat_interval.2.trans manuscriptNormV12_5_rounded_endpoints.2

def manuscriptNormV12_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV12_6SubstituteRat_interval :
    manuscriptNormV12_6SubstituteRat ∈ Set.Icc manuscriptNormV12_6Interval.1 manuscriptNormV12_6Interval.2 := by
  simpa only [manuscriptNormV12_6SubstituteRat, manuscriptNormV12_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_6SubstituteRat_upper :
    manuscriptNormV12_6SubstituteRat ≤ (5545891559125320601256195969 / 500000000000000000000000000000) :=
  manuscriptNormV12_6SubstituteRat_interval.2.trans manuscriptNormV12_6_rounded_endpoints.2

def manuscriptNormV12_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV12_7SubstituteRat_interval :
    manuscriptNormV12_7SubstituteRat ∈ Set.Icc manuscriptNormV12_7Interval.1 manuscriptNormV12_7Interval.2 := by
  simpa only [manuscriptNormV12_7SubstituteRat, manuscriptNormV12_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_7SubstituteRat_upper :
    manuscriptNormV12_7SubstituteRat ≤ (16020904669330418666468974703 / 500000000000000000000000000000) :=
  manuscriptNormV12_7SubstituteRat_interval.2.trans manuscriptNormV12_7_rounded_endpoints.2

def manuscriptNormV12_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV12_8SubstituteRat_interval :
    manuscriptNormV12_8SubstituteRat ∈ Set.Icc manuscriptNormV12_8Interval.1 manuscriptNormV12_8Interval.2 := by
  simpa only [manuscriptNormV12_8SubstituteRat, manuscriptNormV12_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_8SubstituteRat_upper :
    manuscriptNormV12_8SubstituteRat ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) :=
  manuscriptNormV12_8SubstituteRat_interval.2.trans manuscriptNormV12_8_rounded_endpoints.2

def manuscriptNormV12_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV12_9SubstituteRat_interval :
    manuscriptNormV12_9SubstituteRat ∈ Set.Icc manuscriptNormV12_9Interval.1 manuscriptNormV12_9Interval.2 := by
  simpa only [manuscriptNormV12_9SubstituteRat, manuscriptNormV12_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_9SubstituteRat_upper :
    manuscriptNormV12_9SubstituteRat ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) :=
  manuscriptNormV12_9SubstituteRat_interval.2.trans manuscriptNormV12_9_rounded_endpoints.2

def manuscriptNormV12_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV12_10SubstituteRat_interval :
    manuscriptNormV12_10SubstituteRat ∈ Set.Icc manuscriptNormV12_10Interval.1 manuscriptNormV12_10Interval.2 := by
  simpa only [manuscriptNormV12_10SubstituteRat, manuscriptNormV12_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_10SubstituteRat_upper :
    manuscriptNormV12_10SubstituteRat ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) :=
  manuscriptNormV12_10SubstituteRat_interval.2.trans manuscriptNormV12_10_rounded_endpoints.2

def manuscriptNormV12_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV12_11SubstituteRat_interval :
    manuscriptNormV12_11SubstituteRat ∈ Set.Icc manuscriptNormV12_11Interval.1 manuscriptNormV12_11Interval.2 := by
  simpa only [manuscriptNormV12_11SubstituteRat, manuscriptNormV12_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_11SubstituteRat_upper :
    manuscriptNormV12_11SubstituteRat ≤ (4103853551506105342014053837 / 100000000000000000000000000000) :=
  manuscriptNormV12_11SubstituteRat_interval.2.trans manuscriptNormV12_11_rounded_endpoints.2

def manuscriptNormV12_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV12_12SubstituteRat_interval :
    manuscriptNormV12_12SubstituteRat ∈ Set.Icc manuscriptNormV12_12Interval.1 manuscriptNormV12_12Interval.2 := by
  simpa only [manuscriptNormV12_12SubstituteRat, manuscriptNormV12_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormV12_12SubstituteRat_upper :
    manuscriptNormV12_12SubstituteRat ≤ (7911697498379982655265387197 / 1000000000000000000000000000000) :=
  manuscriptNormV12_12SubstituteRat_interval.2.trans manuscriptNormV12_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow12 : ℚ :=
  manuscriptNormV12_0SubstituteRat +
    manuscriptNormV12_1SubstituteRat +
    manuscriptNormV12_2SubstituteRat +
    manuscriptNormV12_3SubstituteRat +
    manuscriptNormV12_4SubstituteRat +
    manuscriptNormV12_5SubstituteRat +
    manuscriptNormV12_6SubstituteRat +
    manuscriptNormV12_7SubstituteRat +
    manuscriptNormV12_8SubstituteRat +
    manuscriptNormV12_9SubstituteRat +
    manuscriptNormV12_10SubstituteRat +
    manuscriptNormV12_11SubstituteRat +
    manuscriptNormV12_12SubstituteRat

theorem manuscriptNormVSubstituteRow12_upper : manuscriptNormVSubstituteRow12 ≤ (59495018237695265878229151011 / 500000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow12
  linarith only [manuscriptNormV12_0SubstituteRat_upper,
    manuscriptNormV12_1SubstituteRat_upper,
    manuscriptNormV12_2SubstituteRat_upper,
    manuscriptNormV12_3SubstituteRat_upper,
    manuscriptNormV12_4SubstituteRat_upper,
    manuscriptNormV12_5SubstituteRat_upper,
    manuscriptNormV12_6SubstituteRat_upper,
    manuscriptNormV12_7SubstituteRat_upper,
    manuscriptNormV12_8SubstituteRat_upper,
    manuscriptNormV12_9SubstituteRat_upper,
    manuscriptNormV12_10SubstituteRat_upper,
    manuscriptNormV12_11SubstituteRat_upper,
    manuscriptNormV12_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV12_0SubstituteRat_composition_error :
    |manuscriptNormV12_0Term - (manuscriptNormV12_0SubstituteRat : ℝ)| ≤ (((37392285633 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_0SubstituteRat ∈ Set.Icc manuscriptNormV12_0Interval.1 manuscriptNormV12_0Interval.2 := by
    simpa only [manuscriptNormV12_0SubstituteRat, manuscriptNormV12_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_0Interval.1 manuscriptNormV12_0Interval.2 manuscriptNormV12_0SubstituteRat
    (10629171334454979986482737241 / 1000000000000000000000000000000) (10629171334454980584759307369 / 1000000000000000000000000000000) manuscriptNormV12_0Term
    manuscriptNormV12_0_exact_interval hq manuscriptNormV12_0_rounded_endpoints.1 manuscriptNormV12_0_rounded_endpoints.2
  have hw : ((10629171334454980584759307369 / 1000000000000000000000000000000) - (10629171334454979986482737241 / 1000000000000000000000000000000) : ℚ) = (37392285633 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_1SubstituteRat_composition_error :
    |manuscriptNormV12_1Term - (manuscriptNormV12_1SubstituteRat : ℝ)| ≤ (((175229584383 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_1SubstituteRat ∈ Set.Icc manuscriptNormV12_1Interval.1 manuscriptNormV12_1Interval.2 := by
    simpa only [manuscriptNormV12_1SubstituteRat, manuscriptNormV12_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_1Interval.1 manuscriptNormV12_1Interval.2 manuscriptNormV12_1SubstituteRat
    (878208501076450742714674087 / 250000000000000000000000000000) (3512834004305803146088280731 / 1000000000000000000000000000000) manuscriptNormV12_1Term
    manuscriptNormV12_1_exact_interval hq manuscriptNormV12_1_rounded_endpoints.1 manuscriptNormV12_1_rounded_endpoints.2
  have hw : ((3512834004305803146088280731 / 1000000000000000000000000000000) - (878208501076450742714674087 / 250000000000000000000000000000) : ℚ) = (175229584383 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_2SubstituteRat_composition_error :
    |manuscriptNormV12_2Term - (manuscriptNormV12_2SubstituteRat : ℝ)| ≤ (((6262052587 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_2SubstituteRat ∈ Set.Icc manuscriptNormV12_2Interval.1 manuscriptNormV12_2Interval.2 := by
    simpa only [manuscriptNormV12_2SubstituteRat, manuscriptNormV12_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_2Interval.1 manuscriptNormV12_2Interval.2 manuscriptNormV12_2SubstituteRat
    (-2045581158108370136473370921 / 1000000000000000000000000000000) (-2045581158108370036280529529 / 1000000000000000000000000000000) manuscriptNormV12_2Term
    manuscriptNormV12_2_exact_interval hq manuscriptNormV12_2_rounded_endpoints.1 manuscriptNormV12_2_rounded_endpoints.2
  have hw : ((-2045581158108370036280529529 / 1000000000000000000000000000000) - (-2045581158108370136473370921 / 1000000000000000000000000000000) : ℚ) = (6262052587 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_3SubstituteRat_composition_error :
    |manuscriptNormV12_3Term - (manuscriptNormV12_3SubstituteRat : ℝ)| ≤ (((194161154693 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_3SubstituteRat ∈ Set.Icc manuscriptNormV12_3Interval.1 manuscriptNormV12_3Interval.2 := by
    simpa only [manuscriptNormV12_3SubstituteRat, manuscriptNormV12_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_3Interval.1 manuscriptNormV12_3Interval.2 manuscriptNormV12_3SubstituteRat
    (4185192971723380656657287637 / 1000000000000000000000000000000) (418519297172338085081844233 / 100000000000000000000000000000) manuscriptNormV12_3Term
    manuscriptNormV12_3_exact_interval hq manuscriptNormV12_3_rounded_endpoints.1 manuscriptNormV12_3_rounded_endpoints.2
  have hw : ((418519297172338085081844233 / 100000000000000000000000000000) - (4185192971723380656657287637 / 1000000000000000000000000000000) : ℚ) = (194161154693 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_4SubstituteRat_composition_error :
    |manuscriptNormV12_4Term - (manuscriptNormV12_4SubstituteRat : ℝ)| ≤ (((457333864503 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_4SubstituteRat ∈ Set.Icc manuscriptNormV12_4Interval.1 manuscriptNormV12_4Interval.2 := by
    simpa only [manuscriptNormV12_4SubstituteRat, manuscriptNormV12_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_4Interval.1 manuscriptNormV12_4Interval.2 manuscriptNormV12_4SubstituteRat
    (-5049556952780585057360689577 / 500000000000000000000000000000) (-10099113905561169657387514651 / 1000000000000000000000000000000) manuscriptNormV12_4Term
    manuscriptNormV12_4_exact_interval hq manuscriptNormV12_4_rounded_endpoints.1 manuscriptNormV12_4_rounded_endpoints.2
  have hw : ((-10099113905561169657387514651 / 1000000000000000000000000000000) - (-5049556952780585057360689577 / 500000000000000000000000000000) : ℚ) = (457333864503 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_5SubstituteRat_composition_error :
    |manuscriptNormV12_5Term - (manuscriptNormV12_5SubstituteRat : ℝ)| ≤ (((7520247413 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_5SubstituteRat ∈ Set.Icc manuscriptNormV12_5Interval.1 manuscriptNormV12_5Interval.2 := by
    simpa only [manuscriptNormV12_5SubstituteRat, manuscriptNormV12_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_5Interval.1 manuscriptNormV12_5Interval.2 manuscriptNormV12_5SubstituteRat
    (4061860828661937773552758353 / 125000000000000000000000000000) (32494886629295502195942314237 / 1000000000000000000000000000000) manuscriptNormV12_5Term
    manuscriptNormV12_5_exact_interval hq manuscriptNormV12_5_rounded_endpoints.1 manuscriptNormV12_5_rounded_endpoints.2
  have hw : ((32494886629295502195942314237 / 1000000000000000000000000000000) - (4061860828661937773552758353 / 125000000000000000000000000000) : ℚ) = (7520247413 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_6SubstituteRat_composition_error :
    |manuscriptNormV12_6Term - (manuscriptNormV12_6SubstituteRat : ℝ)| ≤ (((1314961523 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_6SubstituteRat ∈ Set.Icc manuscriptNormV12_6Interval.1 manuscriptNormV12_6Interval.2 := by
    simpa only [manuscriptNormV12_6SubstituteRat, manuscriptNormV12_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_6Interval.1 manuscriptNormV12_6Interval.2 manuscriptNormV12_6SubstituteRat
    (2218356623650128240239486083 / 200000000000000000000000000000) (5545891559125320601256195969 / 500000000000000000000000000000) manuscriptNormV12_6Term
    manuscriptNormV12_6_exact_interval hq manuscriptNormV12_6_rounded_endpoints.1 manuscriptNormV12_6_rounded_endpoints.2
  have hw : ((5545891559125320601256195969 / 500000000000000000000000000000) - (2218356623650128240239486083 / 200000000000000000000000000000) : ℚ) = (1314961523 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_7SubstituteRat_composition_error :
    |manuscriptNormV12_7Term - (manuscriptNormV12_7SubstituteRat : ℝ)| ≤ (((3492861061 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_7SubstituteRat ∈ Set.Icc manuscriptNormV12_7Interval.1 manuscriptNormV12_7Interval.2 := by
    simpa only [manuscriptNormV12_7SubstituteRat, manuscriptNormV12_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_7Interval.1 manuscriptNormV12_7Interval.2 manuscriptNormV12_7SubstituteRat
    (8010452334665209331488056821 / 250000000000000000000000000000) (16020904669330418666468974703 / 500000000000000000000000000000) manuscriptNormV12_7Term
    manuscriptNormV12_7_exact_interval hq manuscriptNormV12_7_rounded_endpoints.1 manuscriptNormV12_7_rounded_endpoints.2
  have hw : ((16020904669330418666468974703 / 500000000000000000000000000000) - (8010452334665209331488056821 / 250000000000000000000000000000) : ℚ) = (3492861061 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_8SubstituteRat_composition_error :
    |manuscriptNormV12_8Term - (manuscriptNormV12_8SubstituteRat : ℝ)| ≤ (((1217277327 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_8SubstituteRat ∈ Set.Icc manuscriptNormV12_8Interval.1 manuscriptNormV12_8Interval.2 := by
    simpa only [manuscriptNormV12_8SubstituteRat, manuscriptNormV12_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_8Interval.1 manuscriptNormV12_8Interval.2 manuscriptNormV12_8SubstituteRat
    (71351466364959732874330401 / 6250000000000000000000000000) (11416234618393557261110141487 / 1000000000000000000000000000000) manuscriptNormV12_8Term
    manuscriptNormV12_8_exact_interval hq manuscriptNormV12_8_rounded_endpoints.1 manuscriptNormV12_8_rounded_endpoints.2
  have hw : ((11416234618393557261110141487 / 1000000000000000000000000000000) - (71351466364959732874330401 / 6250000000000000000000000000) : ℚ) = (1217277327 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_9SubstituteRat_composition_error :
    |manuscriptNormV12_9Term - (manuscriptNormV12_9SubstituteRat : ℝ)| ≤ (((4149300417 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_9SubstituteRat ∈ Set.Icc manuscriptNormV12_9Interval.1 manuscriptNormV12_9Interval.2 := by
    simpa only [manuscriptNormV12_9SubstituteRat, manuscriptNormV12_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_9Interval.1 manuscriptNormV12_9Interval.2 manuscriptNormV12_9SubstituteRat
    (-9565262706655637646952898537 / 500000000000000000000000000000) (-19130525413311275289756496657 / 1000000000000000000000000000000) manuscriptNormV12_9Term
    manuscriptNormV12_9_exact_interval hq manuscriptNormV12_9_rounded_endpoints.1 manuscriptNormV12_9_rounded_endpoints.2
  have hw : ((-19130525413311275289756496657 / 1000000000000000000000000000000) - (-9565262706655637646952898537 / 500000000000000000000000000000) : ℚ) = (4149300417 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_10SubstituteRat_composition_error :
    |manuscriptNormV12_10Term - (manuscriptNormV12_10SubstituteRat : ℝ)| ≤ (((215141891 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_10SubstituteRat ∈ Set.Icc manuscriptNormV12_10Interval.1 manuscriptNormV12_10Interval.2 := by
    simpa only [manuscriptNormV12_10SubstituteRat, manuscriptNormV12_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_10Interval.1 manuscriptNormV12_10Interval.2 manuscriptNormV12_10SubstituteRat
    (-1014222019038597977530548497 / 250000000000000000000000000000) (-2028444038077195954845955103 / 500000000000000000000000000000) manuscriptNormV12_10Term
    manuscriptNormV12_10_exact_interval hq manuscriptNormV12_10_rounded_endpoints.1 manuscriptNormV12_10_rounded_endpoints.2
  have hw : ((-2028444038077195954845955103 / 500000000000000000000000000000) - (-1014222019038597977530548497 / 250000000000000000000000000000) : ℚ) = (215141891 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_11SubstituteRat_composition_error :
    |manuscriptNormV12_11Term - (manuscriptNormV12_11SubstituteRat : ℝ)| ≤ (((502008027 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_11SubstituteRat ∈ Set.Icc manuscriptNormV12_11Interval.1 manuscriptNormV12_11Interval.2 := by
    simpa only [manuscriptNormV12_11SubstituteRat, manuscriptNormV12_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_11Interval.1 manuscriptNormV12_11Interval.2 manuscriptNormV12_11SubstituteRat
    (20519267757530526706054204969 / 500000000000000000000000000000) (4103853551506105342014053837 / 100000000000000000000000000000) manuscriptNormV12_11Term
    manuscriptNormV12_11_exact_interval hq manuscriptNormV12_11_rounded_endpoints.1 manuscriptNormV12_11_rounded_endpoints.2
  have hw : ((4103853551506105342014053837 / 100000000000000000000000000000) - (20519267757530526706054204969 / 500000000000000000000000000000) : ℚ) = (502008027 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV12_12SubstituteRat_composition_error :
    |manuscriptNormV12_12Term - (manuscriptNormV12_12SubstituteRat : ℝ)| ≤ (((943160181 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV12_12SubstituteRat ∈ Set.Icc manuscriptNormV12_12Interval.1 manuscriptNormV12_12Interval.2 := by
    simpa only [manuscriptNormV12_12SubstituteRat, manuscriptNormV12_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV12_12Interval.1 manuscriptNormV12_12Interval.2 manuscriptNormV12_12SubstituteRat
    (988962187297497831790278377 / 125000000000000000000000000000) (7911697498379982655265387197 / 1000000000000000000000000000000) manuscriptNormV12_12Term
    manuscriptNormV12_12_exact_interval hq manuscriptNormV12_12_rounded_endpoints.1 manuscriptNormV12_12_rounded_endpoints.2
  have hw : ((7911697498379982655265387197 / 1000000000000000000000000000000) - (988962187297497831790278377 / 125000000000000000000000000000) : ℚ) = (943160181 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow12_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 12 (0, 0)) - (manuscriptNormVSubstituteRow12 : ℝ)| ≤ (((194473387037 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV12_0SubstituteRat_composition_error
  have h1 := manuscriptNormV12_1SubstituteRat_composition_error
  have h2 := manuscriptNormV12_2SubstituteRat_composition_error
  have h3 := manuscriptNormV12_3SubstituteRat_composition_error
  have h4 := manuscriptNormV12_4SubstituteRat_composition_error
  have h5 := manuscriptNormV12_5SubstituteRat_composition_error
  have h6 := manuscriptNormV12_6SubstituteRat_composition_error
  have h7 := manuscriptNormV12_7SubstituteRat_composition_error
  have h8 := manuscriptNormV12_8SubstituteRat_composition_error
  have h9 := manuscriptNormV12_9SubstituteRat_composition_error
  have h10 := manuscriptNormV12_10SubstituteRat_composition_error
  have h11 := manuscriptNormV12_11SubstituteRat_composition_error
  have h12 := manuscriptNormV12_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV12_0Term + (manuscriptNormV12_1Term + (manuscriptNormV12_2Term + (manuscriptNormV12_3Term + (manuscriptNormV12_4Term + (manuscriptNormV12_5Term + (manuscriptNormV12_6Term + (manuscriptNormV12_7Term + (manuscriptNormV12_8Term + (manuscriptNormV12_9Term + (manuscriptNormV12_10Term + (manuscriptNormV12_11Term + (manuscriptNormV12_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow12 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow12
  push_cast
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1,
    (abs_le.mp h10).1,
    (abs_le.mp h11).1,
    (abs_le.mp h12).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2,
    (abs_le.mp h10).2,
    (abs_le.mp h11).2,
    (abs_le.mp h12).2]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptNormV12_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV12_0RoundedSubstituteRat_error :
    |(manuscriptNormV12_0SubstituteRat : ℝ) - (manuscriptNormV12_0RoundedSubstituteRat : ℝ)| ≤
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num) (by norm_num)
  have hw : |(((-31237616036943 / 20000000000000000) : ℚ) : ℝ)| + |(((330063770995139 / 20000000000000000) : ℚ) : ℝ)| =
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV12_1RoundedSubstituteRat_error :
    |(manuscriptNormV12_1SubstituteRat : ℝ) - (manuscriptNormV12_1RoundedSubstituteRat : ℝ)| ≤
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num) (by norm_num)
  have hw : |(((-4574556807003 / 10000000000000000) : ℚ) : ℝ)| + |(((48335809895519 / 10000000000000000) : ℚ) : ℝ)| =
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV12_2RoundedSubstituteRat_error :
    |(manuscriptNormV12_2SubstituteRat : ℝ) - (manuscriptNormV12_2RoundedSubstituteRat : ℝ)| ≤
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num) (by norm_num)
  have hw : |(((-2615667529887 / 10000000000000000) : ℚ) : ℝ)| + |(((27637739306451 / 10000000000000000) : ℚ) : ℝ)| =
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV12_3RoundedSubstituteRat_error :
    |(manuscriptNormV12_3SubstituteRat : ℝ) - (manuscriptNormV12_3RoundedSubstituteRat : ℝ)| ≤
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num) (by norm_num)
  have hw : |(((5068806760521 / 10000000000000000) : ℚ) : ℝ)| + |(((-53558167558133 / 10000000000000000) : ℚ) : ℝ)| =
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV12_4RoundedSubstituteRat_error :
    |(manuscriptNormV12_4SubstituteRat : ℝ) - (manuscriptNormV12_4RoundedSubstituteRat : ℝ)| ≤
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num) (by norm_num)
  have hw : |(((-23877787302441 / 20000000000000000) : ℚ) : ℝ)| + |(((252298143070293 / 20000000000000000) : ℚ) : ℝ)| =
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV12_5RoundedSubstituteRat_error :
    |(manuscriptNormV12_5SubstituteRat : ℝ) - (manuscriptNormV12_5RoundedSubstituteRat : ℝ)| ≤
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-445455465826873 / 20000000000000000) : ℚ) : ℝ)| + |(((256246551143909 / 20000000000000000) : ℚ) : ℝ)| =
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV12_6RoundedSubstituteRat_error :
    |(manuscriptNormV12_6SubstituteRat : ℝ) - (manuscriptNormV12_6RoundedSubstituteRat : ℝ)| ≤
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (389474106710791 / 20000000000000000) (335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((389474106710791 / 20000000000000000) : ℚ) : ℝ)| + |(((335265249034277 / 20000000000000000) : ℚ) : ℝ)| =
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV12_7RoundedSubstituteRat_error :
    |(manuscriptNormV12_7SubstituteRat : ℝ) - (manuscriptNormV12_7RoundedSubstituteRat : ℝ)| ≤
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-295581257499211 / 20000000000000000) (-371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-295581257499211 / 20000000000000000) : ℚ) : ℝ)| + |(((-371321316540867 / 20000000000000000) : ℚ) : ℝ)| =
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV12_8RoundedSubstituteRat_error :
    |(manuscriptNormV12_8SubstituteRat : ℝ) - (manuscriptNormV12_8RoundedSubstituteRat : ℝ)| ≤
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((359993860770103 / 20000000000000000) : ℚ) : ℝ)| + |(((-309276931099449 / 20000000000000000) : ℚ) : ℝ)| =
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV12_9RoundedSubstituteRat_error :
    |(manuscriptNormV12_9SubstituteRat : ℝ) - (manuscriptNormV12_9RoundedSubstituteRat : ℝ)| ≤
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((68110340912023 / 10000000000000000) : ℚ) : ℝ)| + |(((-7554608004191 / 2500000000000000) : ℚ) : ℝ)| =
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV12_10RoundedSubstituteRat_error :
    |(manuscriptNormV12_10SubstituteRat : ℝ) - (manuscriptNormV12_10RoundedSubstituteRat : ℝ)| ≤
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2391875533 / 390625000000) : ℚ) : ℝ)| + |(((-8491908331363 / 2000000000000000) : ℚ) : ℝ)| =
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV12_11RoundedSubstituteRat_error :
    |(manuscriptNormV12_11SubstituteRat : ℝ) - (manuscriptNormV12_11RoundedSubstituteRat : ℝ)| ≤
      (((47580199826617 / 4000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-47580199826617 / 4000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((47580199826617 / 4000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV12_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV12_12RoundedSubstituteRat_error :
    |(manuscriptNormV12_12SubstituteRat : ℝ) - (manuscriptNormV12_12RoundedSubstituteRat : ℝ)| ≤
      (((278307793828553 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((58419274664429 / 5000000000000000) : ℚ) : ℝ)| + |(((44630695170837 / 20000000000000000) : ℚ) : ℝ)| =
      (((278307793828553 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow12 : ℚ :=
  manuscriptNormV12_0RoundedSubstituteRat +
    manuscriptNormV12_1RoundedSubstituteRat +
    manuscriptNormV12_2RoundedSubstituteRat +
    manuscriptNormV12_3RoundedSubstituteRat +
    manuscriptNormV12_4RoundedSubstituteRat +
    manuscriptNormV12_5RoundedSubstituteRat +
    manuscriptNormV12_6RoundedSubstituteRat +
    manuscriptNormV12_7RoundedSubstituteRat +
    manuscriptNormV12_8RoundedSubstituteRat +
    manuscriptNormV12_9RoundedSubstituteRat +
    manuscriptNormV12_10RoundedSubstituteRat +
    manuscriptNormV12_11RoundedSubstituteRat +
    manuscriptNormV12_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow12_error :
    |(manuscriptNormVSubstituteRow12 : ℝ) - (manuscriptNormVRoundedSubstituteRow12 : ℝ)| ≤
      (((2301961500583883 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV12_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV12_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV12_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV12_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV12_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV12_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV12_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV12_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV12_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV12_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV12_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV12_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV12_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow12 manuscriptNormVRoundedSubstituteRow12
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1,
    (abs_le.mp h10).1,
    (abs_le.mp h11).1,
    (abs_le.mp h12).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2,
    (abs_le.mp h10).2,
    (abs_le.mp h11).2,
    (abs_le.mp h12).2]

end InternalCatalan

end

end

end OAI

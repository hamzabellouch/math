import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup047
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup048
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup049
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup050
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup051
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV11_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV11_0SubstituteRat_interval :
    manuscriptNormV11_0SubstituteRat ∈ Set.Icc manuscriptNormV11_0Interval.1 manuscriptNormV11_0Interval.2 := by
  simpa only [manuscriptNormV11_0SubstituteRat, manuscriptNormV11_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num))

private theorem manuscriptNormV11_0SubstituteRat_upper :
    manuscriptNormV11_0SubstituteRat ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) :=
  manuscriptNormV11_0SubstituteRat_interval.2.trans manuscriptNormV11_0_rounded_endpoints.2

def manuscriptNormV11_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV11_1SubstituteRat_interval :
    manuscriptNormV11_1SubstituteRat ∈ Set.Icc manuscriptNormV11_1Interval.1 manuscriptNormV11_1Interval.2 := by
  simpa only [manuscriptNormV11_1SubstituteRat, manuscriptNormV11_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num))

private theorem manuscriptNormV11_1SubstituteRat_upper :
    manuscriptNormV11_1SubstituteRat ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) :=
  manuscriptNormV11_1SubstituteRat_interval.2.trans manuscriptNormV11_1_rounded_endpoints.2

def manuscriptNormV11_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV11_2SubstituteRat_interval :
    manuscriptNormV11_2SubstituteRat ∈ Set.Icc manuscriptNormV11_2Interval.1 manuscriptNormV11_2Interval.2 := by
  simpa only [manuscriptNormV11_2SubstituteRat, manuscriptNormV11_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num))

private theorem manuscriptNormV11_2SubstituteRat_upper :
    manuscriptNormV11_2SubstituteRat ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) :=
  manuscriptNormV11_2SubstituteRat_interval.2.trans manuscriptNormV11_2_rounded_endpoints.2

def manuscriptNormV11_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV11_3SubstituteRat_interval :
    manuscriptNormV11_3SubstituteRat ∈ Set.Icc manuscriptNormV11_3Interval.1 manuscriptNormV11_3Interval.2 := by
  simpa only [manuscriptNormV11_3SubstituteRat, manuscriptNormV11_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num))

private theorem manuscriptNormV11_3SubstituteRat_upper :
    manuscriptNormV11_3SubstituteRat ≤ (418519297172338085081844233 / 100000000000000000000000000000) :=
  manuscriptNormV11_3SubstituteRat_interval.2.trans manuscriptNormV11_3_rounded_endpoints.2

def manuscriptNormV11_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV11_4SubstituteRat_interval :
    manuscriptNormV11_4SubstituteRat ∈ Set.Icc manuscriptNormV11_4Interval.1 manuscriptNormV11_4Interval.2 := by
  simpa only [manuscriptNormV11_4SubstituteRat, manuscriptNormV11_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num))

private theorem manuscriptNormV11_4SubstituteRat_upper :
    manuscriptNormV11_4SubstituteRat ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) :=
  manuscriptNormV11_4SubstituteRat_interval.2.trans manuscriptNormV11_4_rounded_endpoints.2

def manuscriptNormV11_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV11_5SubstituteRat_interval :
    manuscriptNormV11_5SubstituteRat ∈ Set.Icc manuscriptNormV11_5Interval.1 manuscriptNormV11_5Interval.2 := by
  simpa only [manuscriptNormV11_5SubstituteRat, manuscriptNormV11_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_5SubstituteRat_upper :
    manuscriptNormV11_5SubstituteRat ≤ (5545891559125320601256195969 / 500000000000000000000000000000) :=
  manuscriptNormV11_5SubstituteRat_interval.2.trans manuscriptNormV11_5_rounded_endpoints.2

def manuscriptNormV11_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV11_6SubstituteRat_interval :
    manuscriptNormV11_6SubstituteRat ∈ Set.Icc manuscriptNormV11_6Interval.1 manuscriptNormV11_6Interval.2 := by
  simpa only [manuscriptNormV11_6SubstituteRat, manuscriptNormV11_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_6SubstituteRat_upper :
    manuscriptNormV11_6SubstituteRat ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) :=
  manuscriptNormV11_6SubstituteRat_interval.2.trans manuscriptNormV11_6_rounded_endpoints.2

def manuscriptNormV11_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV11_7SubstituteRat_interval :
    manuscriptNormV11_7SubstituteRat ∈ Set.Icc manuscriptNormV11_7Interval.1 manuscriptNormV11_7Interval.2 := by
  simpa only [manuscriptNormV11_7SubstituteRat, manuscriptNormV11_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_7SubstituteRat_upper :
    manuscriptNormV11_7SubstituteRat ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) :=
  manuscriptNormV11_7SubstituteRat_interval.2.trans manuscriptNormV11_7_rounded_endpoints.2

def manuscriptNormV11_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV11_8SubstituteRat_interval :
    manuscriptNormV11_8SubstituteRat ∈ Set.Icc manuscriptNormV11_8Interval.1 manuscriptNormV11_8Interval.2 := by
  simpa only [manuscriptNormV11_8SubstituteRat, manuscriptNormV11_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_8SubstituteRat_upper :
    manuscriptNormV11_8SubstituteRat ≤ (16020904669330418666468974703 / 500000000000000000000000000000) :=
  manuscriptNormV11_8SubstituteRat_interval.2.trans manuscriptNormV11_8_rounded_endpoints.2

def manuscriptNormV11_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV11_9SubstituteRat_interval :
    manuscriptNormV11_9SubstituteRat ∈ Set.Icc manuscriptNormV11_9Interval.1 manuscriptNormV11_9Interval.2 := by
  simpa only [manuscriptNormV11_9SubstituteRat, manuscriptNormV11_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_9SubstituteRat_upper :
    manuscriptNormV11_9SubstituteRat ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) :=
  manuscriptNormV11_9SubstituteRat_interval.2.trans manuscriptNormV11_9_rounded_endpoints.2

def manuscriptNormV11_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV11_10SubstituteRat_interval :
    manuscriptNormV11_10SubstituteRat ∈ Set.Icc manuscriptNormV11_10Interval.1 manuscriptNormV11_10Interval.2 := by
  simpa only [manuscriptNormV11_10SubstituteRat, manuscriptNormV11_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_10SubstituteRat_upper :
    manuscriptNormV11_10SubstituteRat ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) :=
  manuscriptNormV11_10SubstituteRat_interval.2.trans manuscriptNormV11_10_rounded_endpoints.2

def manuscriptNormV11_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV11_11SubstituteRat_interval :
    manuscriptNormV11_11SubstituteRat ∈ Set.Icc manuscriptNormV11_11Interval.1 manuscriptNormV11_11Interval.2 := by
  simpa only [manuscriptNormV11_11SubstituteRat, manuscriptNormV11_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_11SubstituteRat_upper :
    manuscriptNormV11_11SubstituteRat ≤ (7911697498379982655265387197 / 1000000000000000000000000000000) :=
  manuscriptNormV11_11SubstituteRat_interval.2.trans manuscriptNormV11_11_rounded_endpoints.2

def manuscriptNormV11_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV11_12SubstituteRat_interval :
    manuscriptNormV11_12SubstituteRat ∈ Set.Icc manuscriptNormV11_12Interval.1 manuscriptNormV11_12Interval.2 := by
  simpa only [manuscriptNormV11_12SubstituteRat, manuscriptNormV11_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormV11_12SubstituteRat_upper :
    manuscriptNormV11_12SubstituteRat ≤ (4103853551506105342014053837 / 100000000000000000000000000000) :=
  manuscriptNormV11_12SubstituteRat_interval.2.trans manuscriptNormV11_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow11 : ℚ :=
  manuscriptNormV11_0SubstituteRat +
    manuscriptNormV11_1SubstituteRat +
    manuscriptNormV11_2SubstituteRat +
    manuscriptNormV11_3SubstituteRat +
    manuscriptNormV11_4SubstituteRat +
    manuscriptNormV11_5SubstituteRat +
    manuscriptNormV11_6SubstituteRat +
    manuscriptNormV11_7SubstituteRat +
    manuscriptNormV11_8SubstituteRat +
    manuscriptNormV11_9SubstituteRat +
    manuscriptNormV11_10SubstituteRat +
    manuscriptNormV11_11SubstituteRat +
    manuscriptNormV11_12SubstituteRat

theorem manuscriptNormVSubstituteRow11_upper : manuscriptNormVSubstituteRow11 ≤ (59495018237695265878229151011 / 500000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow11
  linarith only [manuscriptNormV11_0SubstituteRat_upper,
    manuscriptNormV11_1SubstituteRat_upper,
    manuscriptNormV11_2SubstituteRat_upper,
    manuscriptNormV11_3SubstituteRat_upper,
    manuscriptNormV11_4SubstituteRat_upper,
    manuscriptNormV11_5SubstituteRat_upper,
    manuscriptNormV11_6SubstituteRat_upper,
    manuscriptNormV11_7SubstituteRat_upper,
    manuscriptNormV11_8SubstituteRat_upper,
    manuscriptNormV11_9SubstituteRat_upper,
    manuscriptNormV11_10SubstituteRat_upper,
    manuscriptNormV11_11SubstituteRat_upper,
    manuscriptNormV11_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV11_0SubstituteRat_composition_error :
    |manuscriptNormV11_0Term - (manuscriptNormV11_0SubstituteRat : ℝ)| ≤ (((37392285633 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_0SubstituteRat ∈ Set.Icc manuscriptNormV11_0Interval.1 manuscriptNormV11_0Interval.2 := by
    simpa only [manuscriptNormV11_0SubstituteRat, manuscriptNormV11_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_0Interval.1 manuscriptNormV11_0Interval.2 manuscriptNormV11_0SubstituteRat
    (10629171334454979986482737241 / 1000000000000000000000000000000) (10629171334454980584759307369 / 1000000000000000000000000000000) manuscriptNormV11_0Term
    manuscriptNormV11_0_exact_interval hq manuscriptNormV11_0_rounded_endpoints.1 manuscriptNormV11_0_rounded_endpoints.2
  have hw : ((10629171334454980584759307369 / 1000000000000000000000000000000) - (10629171334454979986482737241 / 1000000000000000000000000000000) : ℚ) = (37392285633 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_1SubstituteRat_composition_error :
    |manuscriptNormV11_1Term - (manuscriptNormV11_1SubstituteRat : ℝ)| ≤ (((175229584383 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_1SubstituteRat ∈ Set.Icc manuscriptNormV11_1Interval.1 manuscriptNormV11_1Interval.2 := by
    simpa only [manuscriptNormV11_1SubstituteRat, manuscriptNormV11_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_1Interval.1 manuscriptNormV11_1Interval.2 manuscriptNormV11_1SubstituteRat
    (878208501076450742714674087 / 250000000000000000000000000000) (3512834004305803146088280731 / 1000000000000000000000000000000) manuscriptNormV11_1Term
    manuscriptNormV11_1_exact_interval hq manuscriptNormV11_1_rounded_endpoints.1 manuscriptNormV11_1_rounded_endpoints.2
  have hw : ((3512834004305803146088280731 / 1000000000000000000000000000000) - (878208501076450742714674087 / 250000000000000000000000000000) : ℚ) = (175229584383 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_2SubstituteRat_composition_error :
    |manuscriptNormV11_2Term - (manuscriptNormV11_2SubstituteRat : ℝ)| ≤ (((6262052587 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_2SubstituteRat ∈ Set.Icc manuscriptNormV11_2Interval.1 manuscriptNormV11_2Interval.2 := by
    simpa only [manuscriptNormV11_2SubstituteRat, manuscriptNormV11_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_2Interval.1 manuscriptNormV11_2Interval.2 manuscriptNormV11_2SubstituteRat
    (-2045581158108370136473370921 / 1000000000000000000000000000000) (-2045581158108370036280529529 / 1000000000000000000000000000000) manuscriptNormV11_2Term
    manuscriptNormV11_2_exact_interval hq manuscriptNormV11_2_rounded_endpoints.1 manuscriptNormV11_2_rounded_endpoints.2
  have hw : ((-2045581158108370036280529529 / 1000000000000000000000000000000) - (-2045581158108370136473370921 / 1000000000000000000000000000000) : ℚ) = (6262052587 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_3SubstituteRat_composition_error :
    |manuscriptNormV11_3Term - (manuscriptNormV11_3SubstituteRat : ℝ)| ≤ (((194161154693 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_3SubstituteRat ∈ Set.Icc manuscriptNormV11_3Interval.1 manuscriptNormV11_3Interval.2 := by
    simpa only [manuscriptNormV11_3SubstituteRat, manuscriptNormV11_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_3Interval.1 manuscriptNormV11_3Interval.2 manuscriptNormV11_3SubstituteRat
    (4185192971723380656657287637 / 1000000000000000000000000000000) (418519297172338085081844233 / 100000000000000000000000000000) manuscriptNormV11_3Term
    manuscriptNormV11_3_exact_interval hq manuscriptNormV11_3_rounded_endpoints.1 manuscriptNormV11_3_rounded_endpoints.2
  have hw : ((418519297172338085081844233 / 100000000000000000000000000000) - (4185192971723380656657287637 / 1000000000000000000000000000000) : ℚ) = (194161154693 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_4SubstituteRat_composition_error :
    |manuscriptNormV11_4Term - (manuscriptNormV11_4SubstituteRat : ℝ)| ≤ (((457333864503 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_4SubstituteRat ∈ Set.Icc manuscriptNormV11_4Interval.1 manuscriptNormV11_4Interval.2 := by
    simpa only [manuscriptNormV11_4SubstituteRat, manuscriptNormV11_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_4Interval.1 manuscriptNormV11_4Interval.2 manuscriptNormV11_4SubstituteRat
    (-5049556952780585057360689577 / 500000000000000000000000000000) (-10099113905561169657387514651 / 1000000000000000000000000000000) manuscriptNormV11_4Term
    manuscriptNormV11_4_exact_interval hq manuscriptNormV11_4_rounded_endpoints.1 manuscriptNormV11_4_rounded_endpoints.2
  have hw : ((-10099113905561169657387514651 / 1000000000000000000000000000000) - (-5049556952780585057360689577 / 500000000000000000000000000000) : ℚ) = (457333864503 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_5SubstituteRat_composition_error :
    |manuscriptNormV11_5Term - (manuscriptNormV11_5SubstituteRat : ℝ)| ≤ (((1314961523 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_5SubstituteRat ∈ Set.Icc manuscriptNormV11_5Interval.1 manuscriptNormV11_5Interval.2 := by
    simpa only [manuscriptNormV11_5SubstituteRat, manuscriptNormV11_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_5Interval.1 manuscriptNormV11_5Interval.2 manuscriptNormV11_5SubstituteRat
    (2218356623650128240239486083 / 200000000000000000000000000000) (5545891559125320601256195969 / 500000000000000000000000000000) manuscriptNormV11_5Term
    manuscriptNormV11_5_exact_interval hq manuscriptNormV11_5_rounded_endpoints.1 manuscriptNormV11_5_rounded_endpoints.2
  have hw : ((5545891559125320601256195969 / 500000000000000000000000000000) - (2218356623650128240239486083 / 200000000000000000000000000000) : ℚ) = (1314961523 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_6SubstituteRat_composition_error :
    |manuscriptNormV11_6Term - (manuscriptNormV11_6SubstituteRat : ℝ)| ≤ (((7520247413 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_6SubstituteRat ∈ Set.Icc manuscriptNormV11_6Interval.1 manuscriptNormV11_6Interval.2 := by
    simpa only [manuscriptNormV11_6SubstituteRat, manuscriptNormV11_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_6Interval.1 manuscriptNormV11_6Interval.2 manuscriptNormV11_6SubstituteRat
    (4061860828661937773552758353 / 125000000000000000000000000000) (32494886629295502195942314237 / 1000000000000000000000000000000) manuscriptNormV11_6Term
    manuscriptNormV11_6_exact_interval hq manuscriptNormV11_6_rounded_endpoints.1 manuscriptNormV11_6_rounded_endpoints.2
  have hw : ((32494886629295502195942314237 / 1000000000000000000000000000000) - (4061860828661937773552758353 / 125000000000000000000000000000) : ℚ) = (7520247413 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_7SubstituteRat_composition_error :
    |manuscriptNormV11_7Term - (manuscriptNormV11_7SubstituteRat : ℝ)| ≤ (((1217277327 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_7SubstituteRat ∈ Set.Icc manuscriptNormV11_7Interval.1 manuscriptNormV11_7Interval.2 := by
    simpa only [manuscriptNormV11_7SubstituteRat, manuscriptNormV11_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_7Interval.1 manuscriptNormV11_7Interval.2 manuscriptNormV11_7SubstituteRat
    (71351466364959732874330401 / 6250000000000000000000000000) (11416234618393557261110141487 / 1000000000000000000000000000000) manuscriptNormV11_7Term
    manuscriptNormV11_7_exact_interval hq manuscriptNormV11_7_rounded_endpoints.1 manuscriptNormV11_7_rounded_endpoints.2
  have hw : ((11416234618393557261110141487 / 1000000000000000000000000000000) - (71351466364959732874330401 / 6250000000000000000000000000) : ℚ) = (1217277327 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_8SubstituteRat_composition_error :
    |manuscriptNormV11_8Term - (manuscriptNormV11_8SubstituteRat : ℝ)| ≤ (((3492861061 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_8SubstituteRat ∈ Set.Icc manuscriptNormV11_8Interval.1 manuscriptNormV11_8Interval.2 := by
    simpa only [manuscriptNormV11_8SubstituteRat, manuscriptNormV11_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_8Interval.1 manuscriptNormV11_8Interval.2 manuscriptNormV11_8SubstituteRat
    (8010452334665209331488056821 / 250000000000000000000000000000) (16020904669330418666468974703 / 500000000000000000000000000000) manuscriptNormV11_8Term
    manuscriptNormV11_8_exact_interval hq manuscriptNormV11_8_rounded_endpoints.1 manuscriptNormV11_8_rounded_endpoints.2
  have hw : ((16020904669330418666468974703 / 500000000000000000000000000000) - (8010452334665209331488056821 / 250000000000000000000000000000) : ℚ) = (3492861061 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_9SubstituteRat_composition_error :
    |manuscriptNormV11_9Term - (manuscriptNormV11_9SubstituteRat : ℝ)| ≤ (((215141891 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_9SubstituteRat ∈ Set.Icc manuscriptNormV11_9Interval.1 manuscriptNormV11_9Interval.2 := by
    simpa only [manuscriptNormV11_9SubstituteRat, manuscriptNormV11_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_9Interval.1 manuscriptNormV11_9Interval.2 manuscriptNormV11_9SubstituteRat
    (-1014222019038597977530548497 / 250000000000000000000000000000) (-2028444038077195954845955103 / 500000000000000000000000000000) manuscriptNormV11_9Term
    manuscriptNormV11_9_exact_interval hq manuscriptNormV11_9_rounded_endpoints.1 manuscriptNormV11_9_rounded_endpoints.2
  have hw : ((-2028444038077195954845955103 / 500000000000000000000000000000) - (-1014222019038597977530548497 / 250000000000000000000000000000) : ℚ) = (215141891 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_10SubstituteRat_composition_error :
    |manuscriptNormV11_10Term - (manuscriptNormV11_10SubstituteRat : ℝ)| ≤ (((4149300417 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_10SubstituteRat ∈ Set.Icc manuscriptNormV11_10Interval.1 manuscriptNormV11_10Interval.2 := by
    simpa only [manuscriptNormV11_10SubstituteRat, manuscriptNormV11_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_10Interval.1 manuscriptNormV11_10Interval.2 manuscriptNormV11_10SubstituteRat
    (-9565262706655637646952898537 / 500000000000000000000000000000) (-19130525413311275289756496657 / 1000000000000000000000000000000) manuscriptNormV11_10Term
    manuscriptNormV11_10_exact_interval hq manuscriptNormV11_10_rounded_endpoints.1 manuscriptNormV11_10_rounded_endpoints.2
  have hw : ((-19130525413311275289756496657 / 1000000000000000000000000000000) - (-9565262706655637646952898537 / 500000000000000000000000000000) : ℚ) = (4149300417 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_11SubstituteRat_composition_error :
    |manuscriptNormV11_11Term - (manuscriptNormV11_11SubstituteRat : ℝ)| ≤ (((943160181 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_11SubstituteRat ∈ Set.Icc manuscriptNormV11_11Interval.1 manuscriptNormV11_11Interval.2 := by
    simpa only [manuscriptNormV11_11SubstituteRat, manuscriptNormV11_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_11Interval.1 manuscriptNormV11_11Interval.2 manuscriptNormV11_11SubstituteRat
    (988962187297497831790278377 / 125000000000000000000000000000) (7911697498379982655265387197 / 1000000000000000000000000000000) manuscriptNormV11_11Term
    manuscriptNormV11_11_exact_interval hq manuscriptNormV11_11_rounded_endpoints.1 manuscriptNormV11_11_rounded_endpoints.2
  have hw : ((7911697498379982655265387197 / 1000000000000000000000000000000) - (988962187297497831790278377 / 125000000000000000000000000000) : ℚ) = (943160181 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV11_12SubstituteRat_composition_error :
    |manuscriptNormV11_12Term - (manuscriptNormV11_12SubstituteRat : ℝ)| ≤ (((502008027 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV11_12SubstituteRat ∈ Set.Icc manuscriptNormV11_12Interval.1 manuscriptNormV11_12Interval.2 := by
    simpa only [manuscriptNormV11_12SubstituteRat, manuscriptNormV11_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV11_12Interval.1 manuscriptNormV11_12Interval.2 manuscriptNormV11_12SubstituteRat
    (20519267757530526706054204969 / 500000000000000000000000000000) (4103853551506105342014053837 / 100000000000000000000000000000) manuscriptNormV11_12Term
    manuscriptNormV11_12_exact_interval hq manuscriptNormV11_12_rounded_endpoints.1 manuscriptNormV11_12_rounded_endpoints.2
  have hw : ((4103853551506105342014053837 / 100000000000000000000000000000) - (20519267757530526706054204969 / 500000000000000000000000000000) : ℚ) = (502008027 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow11_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 11 (0, 0)) - (manuscriptNormVSubstituteRow11 : ℝ)| ≤ (((194473387037 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV11_0SubstituteRat_composition_error
  have h1 := manuscriptNormV11_1SubstituteRat_composition_error
  have h2 := manuscriptNormV11_2SubstituteRat_composition_error
  have h3 := manuscriptNormV11_3SubstituteRat_composition_error
  have h4 := manuscriptNormV11_4SubstituteRat_composition_error
  have h5 := manuscriptNormV11_5SubstituteRat_composition_error
  have h6 := manuscriptNormV11_6SubstituteRat_composition_error
  have h7 := manuscriptNormV11_7SubstituteRat_composition_error
  have h8 := manuscriptNormV11_8SubstituteRat_composition_error
  have h9 := manuscriptNormV11_9SubstituteRat_composition_error
  have h10 := manuscriptNormV11_10SubstituteRat_composition_error
  have h11 := manuscriptNormV11_11SubstituteRat_composition_error
  have h12 := manuscriptNormV11_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV11_0Term + (manuscriptNormV11_1Term + (manuscriptNormV11_2Term + (manuscriptNormV11_3Term + (manuscriptNormV11_4Term + (manuscriptNormV11_5Term + (manuscriptNormV11_6Term + (manuscriptNormV11_7Term + (manuscriptNormV11_8Term + (manuscriptNormV11_9Term + (manuscriptNormV11_10Term + (manuscriptNormV11_11Term + (manuscriptNormV11_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow11 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow11
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

def manuscriptNormV11_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV11_0RoundedSubstituteRat_error :
    |(manuscriptNormV11_0SubstituteRat : ℝ) - (manuscriptNormV11_0RoundedSubstituteRat : ℝ)| ≤
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num) (by norm_num)
  have hw : |(((-31237616036943 / 20000000000000000) : ℚ) : ℝ)| + |(((-330063770995139 / 20000000000000000) : ℚ) : ℝ)| =
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV11_1RoundedSubstituteRat_error :
    |(manuscriptNormV11_1SubstituteRat : ℝ) - (manuscriptNormV11_1RoundedSubstituteRat : ℝ)| ≤
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num) (by norm_num)
  have hw : |(((-4574556807003 / 10000000000000000) : ℚ) : ℝ)| + |(((-48335809895519 / 10000000000000000) : ℚ) : ℝ)| =
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV11_2RoundedSubstituteRat_error :
    |(manuscriptNormV11_2SubstituteRat : ℝ) - (manuscriptNormV11_2RoundedSubstituteRat : ℝ)| ≤
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num) (by norm_num)
  have hw : |(((-2615667529887 / 10000000000000000) : ℚ) : ℝ)| + |(((-27637739306451 / 10000000000000000) : ℚ) : ℝ)| =
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV11_3RoundedSubstituteRat_error :
    |(manuscriptNormV11_3SubstituteRat : ℝ) - (manuscriptNormV11_3RoundedSubstituteRat : ℝ)| ≤
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num) (by norm_num)
  have hw : |(((5068806760521 / 10000000000000000) : ℚ) : ℝ)| + |(((53558167558133 / 10000000000000000) : ℚ) : ℝ)| =
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV11_4RoundedSubstituteRat_error :
    |(manuscriptNormV11_4SubstituteRat : ℝ) - (manuscriptNormV11_4RoundedSubstituteRat : ℝ)| ≤
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num) (by norm_num)
  have hw : |(((-23877787302441 / 20000000000000000) : ℚ) : ℝ)| + |(((-252298143070293 / 20000000000000000) : ℚ) : ℝ)| =
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV11_5RoundedSubstituteRat_error :
    |(manuscriptNormV11_5SubstituteRat : ℝ) - (manuscriptNormV11_5RoundedSubstituteRat : ℝ)| ≤
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((389474106710791 / 20000000000000000) : ℚ) : ℝ)| + |(((-335265249034277 / 20000000000000000) : ℚ) : ℝ)| =
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV11_6RoundedSubstituteRat_error :
    |(manuscriptNormV11_6SubstituteRat : ℝ) - (manuscriptNormV11_6RoundedSubstituteRat : ℝ)| ≤
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-445455465826873 / 20000000000000000) : ℚ) : ℝ)| + |(((-256246551143909 / 20000000000000000) : ℚ) : ℝ)| =
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV11_7RoundedSubstituteRat_error :
    |(manuscriptNormV11_7SubstituteRat : ℝ) - (manuscriptNormV11_7RoundedSubstituteRat : ℝ)| ≤
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (359993860770103 / 20000000000000000) (309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((359993860770103 / 20000000000000000) : ℚ) : ℝ)| + |(((309276931099449 / 20000000000000000) : ℚ) : ℝ)| =
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV11_8RoundedSubstituteRat_error :
    |(manuscriptNormV11_8SubstituteRat : ℝ) - (manuscriptNormV11_8RoundedSubstituteRat : ℝ)| ≤
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-295581257499211 / 20000000000000000) : ℚ) : ℝ)| + |(((371321316540867 / 20000000000000000) : ℚ) : ℝ)| =
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV11_9RoundedSubstituteRat_error :
    |(manuscriptNormV11_9SubstituteRat : ℝ) - (manuscriptNormV11_9RoundedSubstituteRat : ℝ)| ≤
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2391875533 / 390625000000) : ℚ) : ℝ)| + |(((8491908331363 / 2000000000000000) : ℚ) : ℝ)| =
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV11_10RoundedSubstituteRat_error :
    |(manuscriptNormV11_10SubstituteRat : ℝ) - (manuscriptNormV11_10RoundedSubstituteRat : ℝ)| ≤
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((68110340912023 / 10000000000000000) : ℚ) : ℝ)| + |(((7554608004191 / 2500000000000000) : ℚ) : ℝ)| =
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV11_11RoundedSubstituteRat_error :
    |(manuscriptNormV11_11SubstituteRat : ℝ) - (manuscriptNormV11_11RoundedSubstituteRat : ℝ)| ≤
      (((278307793828553 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((58419274664429 / 5000000000000000) : ℚ) : ℝ)| + |(((-44630695170837 / 20000000000000000) : ℚ) : ℝ)| =
      (((278307793828553 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV11_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV11_12RoundedSubstituteRat_error :
    |(manuscriptNormV11_12SubstituteRat : ℝ) - (manuscriptNormV11_12RoundedSubstituteRat : ℝ)| ≤
      (((47580199826617 / 4000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-47580199826617 / 4000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((47580199826617 / 4000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow11 : ℚ :=
  manuscriptNormV11_0RoundedSubstituteRat +
    manuscriptNormV11_1RoundedSubstituteRat +
    manuscriptNormV11_2RoundedSubstituteRat +
    manuscriptNormV11_3RoundedSubstituteRat +
    manuscriptNormV11_4RoundedSubstituteRat +
    manuscriptNormV11_5RoundedSubstituteRat +
    manuscriptNormV11_6RoundedSubstituteRat +
    manuscriptNormV11_7RoundedSubstituteRat +
    manuscriptNormV11_8RoundedSubstituteRat +
    manuscriptNormV11_9RoundedSubstituteRat +
    manuscriptNormV11_10RoundedSubstituteRat +
    manuscriptNormV11_11RoundedSubstituteRat +
    manuscriptNormV11_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow11_error :
    |(manuscriptNormVSubstituteRow11 : ℝ) - (manuscriptNormVRoundedSubstituteRow11 : ℝ)| ≤
      (((2301961500583883 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV11_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV11_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV11_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV11_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV11_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV11_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV11_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV11_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV11_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV11_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV11_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV11_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV11_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow11 manuscriptNormVRoundedSubstituteRow11
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

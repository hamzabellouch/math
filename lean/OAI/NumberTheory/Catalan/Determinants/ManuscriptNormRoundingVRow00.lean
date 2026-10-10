import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup000
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup001
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup002
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup003
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup004
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV0_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1)

private theorem manuscriptNormV0_0SubstituteRat_interval :
    manuscriptNormV0_0SubstituteRat ∈ Set.Icc manuscriptNormV0_0Interval.1 manuscriptNormV0_0Interval.2 := by
  simpa only [manuscriptNormV0_0SubstituteRat, manuscriptNormV0_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1) (by norm_num))

private theorem manuscriptNormV0_0SubstituteRat_upper :
    manuscriptNormV0_0SubstituteRat ≤ (11800889997381276403424736449 / 500000000000000000000000000000) :=
  manuscriptNormV0_0SubstituteRat_interval.2.trans manuscriptNormV0_0_rounded_endpoints.2

def manuscriptNormV0_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV0_1SubstituteRat_interval :
    manuscriptNormV0_1SubstituteRat ∈ Set.Icc manuscriptNormV0_1Interval.1 manuscriptNormV0_1Interval.2 := by
  simpa only [manuscriptNormV0_1SubstituteRat, manuscriptNormV0_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV0_1SubstituteRat_upper :
    manuscriptNormV0_1SubstituteRat ≤ (9885502844684175874559747331 / 1000000000000000000000000000000) :=
  manuscriptNormV0_1SubstituteRat_interval.2.trans manuscriptNormV0_1_rounded_endpoints.2

def manuscriptNormV0_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV0_2SubstituteRat_interval :
    manuscriptNormV0_2SubstituteRat ∈ Set.Icc manuscriptNormV0_2Interval.1 manuscriptNormV0_2Interval.2 := by
  simpa only [manuscriptNormV0_2SubstituteRat, manuscriptNormV0_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormV0_2SubstituteRat_upper :
    manuscriptNormV0_2SubstituteRat ≤ (-103099457200427952149476101 / 50000000000000000000000000000) :=
  manuscriptNormV0_2SubstituteRat_interval.2.trans manuscriptNormV0_2_rounded_endpoints.2

def manuscriptNormV0_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV0_3SubstituteRat_interval :
    manuscriptNormV0_3SubstituteRat ∈ Set.Icc manuscriptNormV0_3Interval.1 manuscriptNormV0_3Interval.2 := by
  simpa only [manuscriptNormV0_3SubstituteRat, manuscriptNormV0_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num))

private theorem manuscriptNormV0_3SubstituteRat_upper :
    manuscriptNormV0_3SubstituteRat ≤ (4238278883534061783907706481 / 1000000000000000000000000000000) :=
  manuscriptNormV0_3SubstituteRat_interval.2.trans manuscriptNormV0_3_rounded_endpoints.2

def manuscriptNormV0_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV0_4SubstituteRat_interval :
    manuscriptNormV0_4SubstituteRat ∈ Set.Icc manuscriptNormV0_4Interval.1 manuscriptNormV0_4Interval.2 := by
  simpa only [manuscriptNormV0_4SubstituteRat, manuscriptNormV0_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num))

private theorem manuscriptNormV0_4SubstituteRat_upper :
    manuscriptNormV0_4SubstituteRat ≤ (-2050703264279718561958939307 / 200000000000000000000000000000) :=
  manuscriptNormV0_4SubstituteRat_interval.2.trans manuscriptNormV0_4_rounded_endpoints.2

def manuscriptNormV0_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV0_5SubstituteRat_interval :
    manuscriptNormV0_5SubstituteRat ∈ Set.Icc manuscriptNormV0_5Interval.1 manuscriptNormV0_5Interval.2 := by
  simpa only [manuscriptNormV0_5SubstituteRat, manuscriptNormV0_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num))

private theorem manuscriptNormV0_5SubstituteRat_upper :
    manuscriptNormV0_5SubstituteRat ≤ (1612117655597126146042737969 / 125000000000000000000000000000) :=
  manuscriptNormV0_5SubstituteRat_interval.2.trans manuscriptNormV0_5_rounded_endpoints.2

def manuscriptNormV0_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203)

private theorem manuscriptNormV0_6SubstituteRat_interval :
    manuscriptNormV0_6SubstituteRat ∈ Set.Icc manuscriptNormV0_6Interval.1 manuscriptNormV0_6Interval.2 := by
  simpa only [manuscriptNormV0_6SubstituteRat, manuscriptNormV0_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203) (by norm_num))

private theorem manuscriptNormV0_6SubstituteRat_upper :
    manuscriptNormV0_6SubstituteRat ≤ (1612117655597126146042737969 / 125000000000000000000000000000) :=
  manuscriptNormV0_6SubstituteRat_interval.2.trans manuscriptNormV0_6_rounded_endpoints.2

def manuscriptNormV0_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43)

private theorem manuscriptNormV0_7SubstituteRat_interval :
    manuscriptNormV0_7SubstituteRat ∈ Set.Icc manuscriptNormV0_7Interval.1 manuscriptNormV0_7Interval.2 := by
  simpa only [manuscriptNormV0_7SubstituteRat, manuscriptNormV0_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43) (by norm_num))

private theorem manuscriptNormV0_7SubstituteRat_upper :
    manuscriptNormV0_7SubstituteRat ≤ (3858078394234498723893081383 / 200000000000000000000000000000) :=
  manuscriptNormV0_7SubstituteRat_interval.2.trans manuscriptNormV0_7_rounded_endpoints.2

def manuscriptNormV0_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV0_8SubstituteRat_interval :
    manuscriptNormV0_8SubstituteRat ∈ Set.Icc manuscriptNormV0_8Interval.1 manuscriptNormV0_8Interval.2 := by
  simpa only [manuscriptNormV0_8SubstituteRat, manuscriptNormV0_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num))

private theorem manuscriptNormV0_8SubstituteRat_upper :
    manuscriptNormV0_8SubstituteRat ≤ (3858078394234498723893081383 / 200000000000000000000000000000) :=
  manuscriptNormV0_8SubstituteRat_interval.2.trans manuscriptNormV0_8_rounded_endpoints.2

def manuscriptNormV0_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441)

private theorem manuscriptNormV0_9SubstituteRat_interval :
    manuscriptNormV0_9SubstituteRat ∈ Set.Icc manuscriptNormV0_9Interval.1 manuscriptNormV0_9Interval.2 := by
  simpa only [manuscriptNormV0_9SubstituteRat, manuscriptNormV0_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441) (by norm_num))

private theorem manuscriptNormV0_9SubstituteRat_upper :
    manuscriptNormV0_9SubstituteRat ≤ (-592090129958566250568464173 / 125000000000000000000000000000) :=
  manuscriptNormV0_9SubstituteRat_interval.2.trans manuscriptNormV0_9_rounded_endpoints.2

def manuscriptNormV0_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV0_10SubstituteRat_interval :
    manuscriptNormV0_10SubstituteRat ∈ Set.Icc manuscriptNormV0_10Interval.1 manuscriptNormV0_10Interval.2 := by
  simpa only [manuscriptNormV0_10SubstituteRat, manuscriptNormV0_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num))

private theorem manuscriptNormV0_10SubstituteRat_upper :
    manuscriptNormV0_10SubstituteRat ≤ (-592090129958566250568464173 / 125000000000000000000000000000) :=
  manuscriptNormV0_10SubstituteRat_interval.2.trans manuscriptNormV0_10_rounded_endpoints.2

def manuscriptNormV0_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV0_11SubstituteRat_interval :
    manuscriptNormV0_11SubstituteRat ∈ Set.Icc manuscriptNormV0_11Interval.1 manuscriptNormV0_11Interval.2 := by
  simpa only [manuscriptNormV0_11SubstituteRat, manuscriptNormV0_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num))

private theorem manuscriptNormV0_11SubstituteRat_upper :
    manuscriptNormV0_11SubstituteRat ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) :=
  manuscriptNormV0_11SubstituteRat_interval.2.trans manuscriptNormV0_11_rounded_endpoints.2

def manuscriptNormV0_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV0_12SubstituteRat_interval :
    manuscriptNormV0_12SubstituteRat ∈ Set.Icc manuscriptNormV0_12Interval.1 manuscriptNormV0_12Interval.2 := by
  simpa only [manuscriptNormV0_12SubstituteRat, manuscriptNormV0_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num))

private theorem manuscriptNormV0_12SubstituteRat_upper :
    manuscriptNormV0_12SubstituteRat ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) :=
  manuscriptNormV0_12SubstituteRat_interval.2.trans manuscriptNormV0_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow0 : ℚ :=
  manuscriptNormV0_0SubstituteRat +
    manuscriptNormV0_1SubstituteRat +
    manuscriptNormV0_2SubstituteRat +
    manuscriptNormV0_3SubstituteRat +
    manuscriptNormV0_4SubstituteRat +
    manuscriptNormV0_5SubstituteRat +
    manuscriptNormV0_6SubstituteRat +
    manuscriptNormV0_7SubstituteRat +
    manuscriptNormV0_8SubstituteRat +
    manuscriptNormV0_9SubstituteRat +
    manuscriptNormV0_10SubstituteRat +
    manuscriptNormV0_11SubstituteRat +
    manuscriptNormV0_12SubstituteRat

theorem manuscriptNormVSubstituteRow0_upper : manuscriptNormVSubstituteRow0 ≤ (101569623279045545348570517459 / 1000000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow0
  linarith only [manuscriptNormV0_0SubstituteRat_upper,
    manuscriptNormV0_1SubstituteRat_upper,
    manuscriptNormV0_2SubstituteRat_upper,
    manuscriptNormV0_3SubstituteRat_upper,
    manuscriptNormV0_4SubstituteRat_upper,
    manuscriptNormV0_5SubstituteRat_upper,
    manuscriptNormV0_6SubstituteRat_upper,
    manuscriptNormV0_7SubstituteRat_upper,
    manuscriptNormV0_8SubstituteRat_upper,
    manuscriptNormV0_9SubstituteRat_upper,
    manuscriptNormV0_10SubstituteRat_upper,
    manuscriptNormV0_11SubstituteRat_upper,
    manuscriptNormV0_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV0_0SubstituteRat_composition_error :
    |manuscriptNormV0_0Term - (manuscriptNormV0_0SubstituteRat : ℝ)| ≤ (((1169951141 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_0SubstituteRat ∈ Set.Icc manuscriptNormV0_0Interval.1 manuscriptNormV0_0Interval.2 := by
    simpa only [manuscriptNormV0_0SubstituteRat, manuscriptNormV0_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_0Interval.1 manuscriptNormV0_0Interval.2 manuscriptNormV0_0SubstituteRat
    (11800889997381276401084834167 / 500000000000000000000000000000) (11800889997381276403424736449 / 500000000000000000000000000000) manuscriptNormV0_0Term
    manuscriptNormV0_0_exact_interval hq manuscriptNormV0_0_rounded_endpoints.1 manuscriptNormV0_0_rounded_endpoints.2
  have hw : ((11800889997381276403424736449 / 500000000000000000000000000000) - (11800889997381276401084834167 / 500000000000000000000000000000) : ℚ) = (1169951141 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_1SubstituteRat_composition_error :
    |manuscriptNormV0_1Term - (manuscriptNormV0_1SubstituteRat : ℝ)| ≤ (((285565383 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_1SubstituteRat ∈ Set.Icc manuscriptNormV0_1Interval.1 manuscriptNormV0_1Interval.2 := by
    simpa only [manuscriptNormV0_1SubstituteRat, manuscriptNormV0_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_1Interval.1 manuscriptNormV0_1Interval.2 manuscriptNormV0_1SubstituteRat
    (9885502844684175872275224267 / 1000000000000000000000000000000) (9885502844684175874559747331 / 1000000000000000000000000000000) manuscriptNormV0_1Term
    manuscriptNormV0_1_exact_interval hq manuscriptNormV0_1_rounded_endpoints.1 manuscriptNormV0_1_rounded_endpoints.2
  have hw : ((9885502844684175874559747331 / 1000000000000000000000000000000) - (9885502844684175872275224267 / 1000000000000000000000000000000) : ℚ) = (285565383 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_2SubstituteRat_composition_error :
    |manuscriptNormV0_2Term - (manuscriptNormV0_2SubstituteRat : ℝ)| ≤ (((65310217 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_2SubstituteRat ∈ Set.Icc manuscriptNormV0_2Interval.1 manuscriptNormV0_2Interval.2 := by
    simpa only [manuscriptNormV0_2SubstituteRat, manuscriptNormV0_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_2Interval.1 manuscriptNormV0_2Interval.2 manuscriptNormV0_2SubstituteRat
    (-257748643001069880406345361 / 125000000000000000000000000000) (-103099457200427952149476101 / 50000000000000000000000000000) manuscriptNormV0_2Term
    manuscriptNormV0_2_exact_interval hq manuscriptNormV0_2_rounded_endpoints.1 manuscriptNormV0_2_rounded_endpoints.2
  have hw : ((-103099457200427952149476101 / 50000000000000000000000000000) - (-257748643001069880406345361 / 125000000000000000000000000000) : ℚ) = (65310217 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_3SubstituteRat_composition_error :
    |manuscriptNormV0_3Term - (manuscriptNormV0_3SubstituteRat : ℝ)| ≤ (((506249199 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_3SubstituteRat ∈ Set.Icc manuscriptNormV0_3Interval.1 manuscriptNormV0_3Interval.2 := by
    simpa only [manuscriptNormV0_3SubstituteRat, manuscriptNormV0_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_3Interval.1 manuscriptNormV0_3Interval.2 manuscriptNormV0_3SubstituteRat
    (2119139441767030891700728641 / 500000000000000000000000000000) (4238278883534061783907706481 / 1000000000000000000000000000000) manuscriptNormV0_3Term
    manuscriptNormV0_3_exact_interval hq manuscriptNormV0_3_rounded_endpoints.1 manuscriptNormV0_3_rounded_endpoints.2
  have hw : ((4238278883534061783907706481 / 1000000000000000000000000000000) - (2119139441767030891700728641 / 500000000000000000000000000000) : ℚ) = (506249199 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_4SubstituteRat_composition_error :
    |manuscriptNormV0_4Term - (manuscriptNormV0_4SubstituteRat : ℝ)| ≤ (((596201549 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_4SubstituteRat ∈ Set.Icc manuscriptNormV0_4Interval.1 manuscriptNormV0_4Interval.2 := by
    simpa only [manuscriptNormV0_4SubstituteRat, manuscriptNormV0_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_4Interval.1 manuscriptNormV0_4Interval.2 manuscriptNormV0_4SubstituteRat
    (-10253516321398592810987099633 / 1000000000000000000000000000000) (-2050703264279718561958939307 / 200000000000000000000000000000) manuscriptNormV0_4Term
    manuscriptNormV0_4_exact_interval hq manuscriptNormV0_4_rounded_endpoints.1 manuscriptNormV0_4_rounded_endpoints.2
  have hw : ((-2050703264279718561958939307 / 200000000000000000000000000000) - (-10253516321398592810987099633 / 1000000000000000000000000000000) : ℚ) = (596201549 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_5SubstituteRat_composition_error :
    |manuscriptNormV0_5Term - (manuscriptNormV0_5SubstituteRat : ℝ)| ≤ (((1059249365143 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_5SubstituteRat ∈ Set.Icc manuscriptNormV0_5Interval.1 manuscriptNormV0_5Interval.2 := by
    simpa only [manuscriptNormV0_5SubstituteRat, manuscriptNormV0_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_5Interval.1 manuscriptNormV0_5Interval.2 manuscriptNormV0_5SubstituteRat
    (12896941244777008109092538609 / 1000000000000000000000000000000) (1612117655597126146042737969 / 125000000000000000000000000000) manuscriptNormV0_5Term
    manuscriptNormV0_5_exact_interval hq manuscriptNormV0_5_rounded_endpoints.1 manuscriptNormV0_5_rounded_endpoints.2
  have hw : ((1612117655597126146042737969 / 125000000000000000000000000000) - (12896941244777008109092538609 / 1000000000000000000000000000000) : ℚ) = (1059249365143 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_6SubstituteRat_composition_error :
    |manuscriptNormV0_6Term - (manuscriptNormV0_6SubstituteRat : ℝ)| ≤ (((1059249365143 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_6SubstituteRat ∈ Set.Icc manuscriptNormV0_6Interval.1 manuscriptNormV0_6Interval.2 := by
    simpa only [manuscriptNormV0_6SubstituteRat, manuscriptNormV0_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_6Interval.1 manuscriptNormV0_6Interval.2 manuscriptNormV0_6SubstituteRat
    (12896941244777008109092538609 / 1000000000000000000000000000000) (1612117655597126146042737969 / 125000000000000000000000000000) manuscriptNormV0_6Term
    manuscriptNormV0_6_exact_interval hq manuscriptNormV0_6_rounded_endpoints.1 manuscriptNormV0_6_rounded_endpoints.2
  have hw : ((1612117655597126146042737969 / 125000000000000000000000000000) - (12896941244777008109092538609 / 1000000000000000000000000000000) : ℚ) = (1059249365143 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_7SubstituteRat_composition_error :
    |manuscriptNormV0_7Term - (manuscriptNormV0_7SubstituteRat : ℝ)| ≤ (((831707907701 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_7SubstituteRat ∈ Set.Icc manuscriptNormV0_7Interval.1 manuscriptNormV0_7Interval.2 := by
    simpa only [manuscriptNormV0_7SubstituteRat, manuscriptNormV0_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_7Interval.1 manuscriptNormV0_7Interval.2 manuscriptNormV0_7SubstituteRat
    (9645195985586246393878749607 / 500000000000000000000000000000) (3858078394234498723893081383 / 200000000000000000000000000000) manuscriptNormV0_7Term
    manuscriptNormV0_7_exact_interval hq manuscriptNormV0_7_rounded_endpoints.1 manuscriptNormV0_7_rounded_endpoints.2
  have hw : ((3858078394234498723893081383 / 200000000000000000000000000000) - (9645195985586246393878749607 / 500000000000000000000000000000) : ℚ) = (831707907701 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_8SubstituteRat_composition_error :
    |manuscriptNormV0_8Term - (manuscriptNormV0_8SubstituteRat : ℝ)| ≤ (((831707907701 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_8SubstituteRat ∈ Set.Icc manuscriptNormV0_8Interval.1 manuscriptNormV0_8Interval.2 := by
    simpa only [manuscriptNormV0_8SubstituteRat, manuscriptNormV0_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_8Interval.1 manuscriptNormV0_8Interval.2 manuscriptNormV0_8SubstituteRat
    (9645195985586246393878749607 / 500000000000000000000000000000) (3858078394234498723893081383 / 200000000000000000000000000000) manuscriptNormV0_8Term
    manuscriptNormV0_8_exact_interval hq manuscriptNormV0_8_rounded_endpoints.1 manuscriptNormV0_8_rounded_endpoints.2
  have hw : ((3858078394234498723893081383 / 200000000000000000000000000000) - (9645195985586246393878749607 / 500000000000000000000000000000) : ℚ) = (831707907701 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_9SubstituteRat_composition_error :
    |manuscriptNormV0_9Term - (manuscriptNormV0_9SubstituteRat : ℝ)| ≤ (((41023162771 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_9SubstituteRat ∈ Set.Icc manuscriptNormV0_9Interval.1 manuscriptNormV0_9Interval.2 := by
    simpa only [manuscriptNormV0_9SubstituteRat, manuscriptNormV0_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_9Interval.1 manuscriptNormV0_9Interval.2 manuscriptNormV0_9SubstituteRat
    (-9251408280602598306119171 / 1953125000000000000000000000) (-592090129958566250568464173 / 125000000000000000000000000000) manuscriptNormV0_9Term
    manuscriptNormV0_9_exact_interval hq manuscriptNormV0_9_rounded_endpoints.1 manuscriptNormV0_9_rounded_endpoints.2
  have hw : ((-592090129958566250568464173 / 125000000000000000000000000000) - (-9251408280602598306119171 / 1953125000000000000000000000) : ℚ) = (41023162771 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_10SubstituteRat_composition_error :
    |manuscriptNormV0_10Term - (manuscriptNormV0_10SubstituteRat : ℝ)| ≤ (((41023162771 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_10SubstituteRat ∈ Set.Icc manuscriptNormV0_10Interval.1 manuscriptNormV0_10Interval.2 := by
    simpa only [manuscriptNormV0_10SubstituteRat, manuscriptNormV0_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_10Interval.1 manuscriptNormV0_10Interval.2 manuscriptNormV0_10SubstituteRat
    (-9251408280602598306119171 / 1953125000000000000000000000) (-592090129958566250568464173 / 125000000000000000000000000000) manuscriptNormV0_10Term
    manuscriptNormV0_10_exact_interval hq manuscriptNormV0_10_rounded_endpoints.1 manuscriptNormV0_10_rounded_endpoints.2
  have hw : ((-592090129958566250568464173 / 125000000000000000000000000000) - (-9251408280602598306119171 / 1953125000000000000000000000) : ℚ) = (41023162771 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_11SubstituteRat_composition_error :
    |manuscriptNormV0_11Term - (manuscriptNormV0_11SubstituteRat : ℝ)| ≤ (((37392285633 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_11SubstituteRat ∈ Set.Icc manuscriptNormV0_11Interval.1 manuscriptNormV0_11Interval.2 := by
    simpa only [manuscriptNormV0_11SubstituteRat, manuscriptNormV0_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_11Interval.1 manuscriptNormV0_11Interval.2 manuscriptNormV0_11SubstituteRat
    (10629171334454979986482737241 / 1000000000000000000000000000000) (10629171334454980584759307369 / 1000000000000000000000000000000) manuscriptNormV0_11Term
    manuscriptNormV0_11_exact_interval hq manuscriptNormV0_11_rounded_endpoints.1 manuscriptNormV0_11_rounded_endpoints.2
  have hw : ((10629171334454980584759307369 / 1000000000000000000000000000000) - (10629171334454979986482737241 / 1000000000000000000000000000000) : ℚ) = (37392285633 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV0_12SubstituteRat_composition_error :
    |manuscriptNormV0_12Term - (manuscriptNormV0_12SubstituteRat : ℝ)| ≤ (((37392285633 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV0_12SubstituteRat ∈ Set.Icc manuscriptNormV0_12Interval.1 manuscriptNormV0_12Interval.2 := by
    simpa only [manuscriptNormV0_12SubstituteRat, manuscriptNormV0_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV0_12Interval.1 manuscriptNormV0_12Interval.2 manuscriptNormV0_12SubstituteRat
    (10629171334454979986482737241 / 1000000000000000000000000000000) (10629171334454980584759307369 / 1000000000000000000000000000000) manuscriptNormV0_12Term
    manuscriptNormV0_12_exact_interval hq manuscriptNormV0_12_rounded_endpoints.1 manuscriptNormV0_12_rounded_endpoints.2
  have hw : ((10629171334454980584759307369 / 1000000000000000000000000000000) - (10629171334454979986482737241 / 1000000000000000000000000000000) : ℚ) = (37392285633 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow0_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 0 (0, 0)) - (manuscriptNormVSubstituteRow0 : ℝ)| ≤ (((5643762511073 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV0_0SubstituteRat_composition_error
  have h1 := manuscriptNormV0_1SubstituteRat_composition_error
  have h2 := manuscriptNormV0_2SubstituteRat_composition_error
  have h3 := manuscriptNormV0_3SubstituteRat_composition_error
  have h4 := manuscriptNormV0_4SubstituteRat_composition_error
  have h5 := manuscriptNormV0_5SubstituteRat_composition_error
  have h6 := manuscriptNormV0_6SubstituteRat_composition_error
  have h7 := manuscriptNormV0_7SubstituteRat_composition_error
  have h8 := manuscriptNormV0_8SubstituteRat_composition_error
  have h9 := manuscriptNormV0_9SubstituteRat_composition_error
  have h10 := manuscriptNormV0_10SubstituteRat_composition_error
  have h11 := manuscriptNormV0_11SubstituteRat_composition_error
  have h12 := manuscriptNormV0_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV0_0Term + (manuscriptNormV0_1Term + (manuscriptNormV0_2Term + (manuscriptNormV0_3Term + (manuscriptNormV0_4Term + (manuscriptNormV0_5Term + (manuscriptNormV0_6Term + (manuscriptNormV0_7Term + (manuscriptNormV0_8Term + (manuscriptNormV0_9Term + (manuscriptNormV0_10Term + (manuscriptNormV0_11Term + (manuscriptNormV0_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow0 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow0
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

def manuscriptNormV0_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1)

private theorem manuscriptNormV0_0RoundedSubstituteRat_error :
    |(manuscriptNormV0_0SubstituteRat : ℝ) - (manuscriptNormV0_0RoundedSubstituteRat : ℝ)| ≤
      (((231016015022521 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-231016015022521 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((231016015022521 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV0_1RoundedSubstituteRat_error :
    |(manuscriptNormV0_1SubstituteRat : ℝ) - (manuscriptNormV0_1RoundedSubstituteRat : ℝ)| ≤
      (((33830875019341 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-33830875019341 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((33830875019341 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV0_2RoundedSubstituteRat_error :
    |(manuscriptNormV0_2SubstituteRat : ℝ) - (manuscriptNormV0_2RoundedSubstituteRat : ℝ)| ≤
      (((19344020640489 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-19344020640489 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((19344020640489 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV0_3RoundedSubstituteRat_error :
    |(manuscriptNormV0_3SubstituteRat : ℝ) - (manuscriptNormV0_3RoundedSubstituteRat : ℝ)| ≤
      (((37486072475887 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((37486072475887 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((37486072475887 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV0_4RoundedSubstituteRat_error :
    |(manuscriptNormV0_4SubstituteRat : ℝ) - (manuscriptNormV0_4RoundedSubstituteRat : ℝ)| ≤
      (((176586819674127 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-176586819674127 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((176586819674127 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV0_5RoundedSubstituteRat_error :
    |(manuscriptNormV0_5SubstituteRat : ℝ) - (manuscriptNormV0_5RoundedSubstituteRat : ℝ)| ≤
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num) (by norm_num)
  have hw : |(((-207003480727327 / 10000000000000000) : ℚ) : ℝ)| + |(((-9130910809039 / 312500000000000) : ℚ) : ℝ)| =
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203)

private theorem manuscriptNormV0_6RoundedSubstituteRat_error :
    |(manuscriptNormV0_6SubstituteRat : ℝ) - (manuscriptNormV0_6RoundedSubstituteRat : ℝ)| ≤
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203) (by norm_num) (by norm_num)
  have hw : |(((-207003480727327 / 10000000000000000) : ℚ) : ℝ)| + |(((9130910809039 / 312500000000000) : ℚ) : ℝ)| =
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43)

private theorem manuscriptNormV0_7RoundedSubstituteRat_error :
    |(manuscriptNormV0_7SubstituteRat : ℝ) - (manuscriptNormV0_7RoundedSubstituteRat : ℝ)| ≤
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (119089937171181 / 5000000000000000) (-229422864123923 / 10000000000000000) (0) (1) (949 / 625) (-7 / 43) (by norm_num) (by norm_num)
  have hw : |(((119089937171181 / 5000000000000000) : ℚ) : ℝ)| + |(((-229422864123923 / 10000000000000000) : ℚ) : ℝ)| =
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV0_8RoundedSubstituteRat_error :
    |(manuscriptNormV0_8SubstituteRat : ℝ) - (manuscriptNormV0_8RoundedSubstituteRat : ℝ)| ≤
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num) (by norm_num)
  have hw : |(((119089937171181 / 5000000000000000) : ℚ) : ℝ)| + |(((229422864123923 / 10000000000000000) : ℚ) : ℝ)| =
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441)

private theorem manuscriptNormV0_9RoundedSubstituteRat_error :
    |(manuscriptNormV0_9SubstituteRat : ℝ) - (manuscriptNormV0_9RoundedSubstituteRat : ℝ)| ≤
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441) (by norm_num) (by norm_num)
  have hw : |(((50868278597681 / 10000000000000000) : ℚ) : ℝ)| + |(((90528431015797 / 10000000000000000) : ℚ) : ℝ)| =
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV0_10RoundedSubstituteRat_error :
    |(manuscriptNormV0_10SubstituteRat : ℝ) - (manuscriptNormV0_10RoundedSubstituteRat : ℝ)| ≤
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num) (by norm_num)
  have hw : |(((50868278597681 / 10000000000000000) : ℚ) : ℝ)| + |(((-90528431015797 / 10000000000000000) : ℚ) : ℝ)| =
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV0_11RoundedSubstituteRat_error :
    |(manuscriptNormV0_11SubstituteRat : ℝ) - (manuscriptNormV0_11RoundedSubstituteRat : ℝ)| ≤
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117) (by norm_num) (by norm_num)
  have hw : |(((-31237616036943 / 20000000000000000) : ℚ) : ℝ)| + |(((-330063770995139 / 20000000000000000) : ℚ) : ℝ)| =
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV0_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117)

private theorem manuscriptNormV0_12RoundedSubstituteRat_error :
    |(manuscriptNormV0_12SubstituteRat : ℝ) - (manuscriptNormV0_12RoundedSubstituteRat : ℝ)| ≤
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-31237616036943 / 20000000000000000) (330063770995139 / 20000000000000000) (0) (-1) (632689 / 390625) (133 / 1117) (by norm_num) (by norm_num)
  have hw : |(((-31237616036943 / 20000000000000000) : ℚ) : ℝ)| + |(((330063770995139 / 20000000000000000) : ℚ) : ℝ)| =
      (((180650693516041 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow0 : ℚ :=
  manuscriptNormV0_0RoundedSubstituteRat +
    manuscriptNormV0_1RoundedSubstituteRat +
    manuscriptNormV0_2RoundedSubstituteRat +
    manuscriptNormV0_3RoundedSubstituteRat +
    manuscriptNormV0_4RoundedSubstituteRat +
    manuscriptNormV0_5RoundedSubstituteRat +
    manuscriptNormV0_6RoundedSubstituteRat +
    manuscriptNormV0_7RoundedSubstituteRat +
    manuscriptNormV0_8RoundedSubstituteRat +
    manuscriptNormV0_9RoundedSubstituteRat +
    manuscriptNormV0_10RoundedSubstituteRat +
    manuscriptNormV0_11RoundedSubstituteRat +
    manuscriptNormV0_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow0_error :
    |(manuscriptNormVSubstituteRow0 : ℝ) - (manuscriptNormVRoundedSubstituteRow0 : ℝ)| ≤
      (((79165257684821 / 250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV0_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV0_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV0_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV0_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV0_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV0_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV0_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV0_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV0_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV0_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV0_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV0_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV0_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow0 manuscriptNormVRoundedSubstituteRow0
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

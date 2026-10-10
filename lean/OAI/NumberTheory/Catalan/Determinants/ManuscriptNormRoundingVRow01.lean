import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup004
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup005
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup006
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup007
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup008
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV1_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV1_0SubstituteRat_interval :
    manuscriptNormV1_0SubstituteRat ∈ Set.Icc manuscriptNormV1_0Interval.1 manuscriptNormV1_0Interval.2 := by
  simpa only [manuscriptNormV1_0SubstituteRat, manuscriptNormV1_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV1_0SubstituteRat_upper :
    manuscriptNormV1_0SubstituteRat ≤ (9885502844684175874559747331 / 1000000000000000000000000000000) :=
  manuscriptNormV1_0SubstituteRat_interval.2.trans manuscriptNormV1_0_rounded_endpoints.2

def manuscriptNormV1_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1)

private theorem manuscriptNormV1_1SubstituteRat_interval :
    manuscriptNormV1_1SubstituteRat ∈ Set.Icc manuscriptNormV1_1Interval.1 manuscriptNormV1_1Interval.2 := by
  simpa only [manuscriptNormV1_1SubstituteRat, manuscriptNormV1_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV1_1SubstituteRat_upper :
    manuscriptNormV1_1SubstituteRat ≤ (5045347153041998580067454651 / 1000000000000000000000000000000) :=
  manuscriptNormV1_1SubstituteRat_interval.2.trans manuscriptNormV1_1_rounded_endpoints.2

def manuscriptNormV1_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV1_2SubstituteRat_interval :
    manuscriptNormV1_2SubstituteRat ∈ Set.Icc manuscriptNormV1_2Interval.1 manuscriptNormV1_2Interval.2 := by
  simpa only [manuscriptNormV1_2SubstituteRat, manuscriptNormV1_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num))

private theorem manuscriptNormV1_2SubstituteRat_upper :
    manuscriptNormV1_2SubstituteRat ≤ (-693892837680188433904874467 / 1000000000000000000000000000000) :=
  manuscriptNormV1_2SubstituteRat_interval.2.trans manuscriptNormV1_2_rounded_endpoints.2

def manuscriptNormV1_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV1_3SubstituteRat_interval :
    manuscriptNormV1_3SubstituteRat ∈ Set.Icc manuscriptNormV1_3Interval.1 manuscriptNormV1_3Interval.2 := by
  simpa only [manuscriptNormV1_3SubstituteRat, manuscriptNormV1_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormV1_3SubstituteRat_upper :
    manuscriptNormV1_3SubstituteRat ≤ (1423234542328589038633585387 / 1000000000000000000000000000000) :=
  manuscriptNormV1_3SubstituteRat_interval.2.trans manuscriptNormV1_3_rounded_endpoints.2

def manuscriptNormV1_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV1_4SubstituteRat_interval :
    manuscriptNormV1_4SubstituteRat ∈ Set.Icc manuscriptNormV1_4Interval.1 manuscriptNormV1_4Interval.2 := by
  simpa only [manuscriptNormV1_4SubstituteRat, manuscriptNormV1_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num))

private theorem manuscriptNormV1_4SubstituteRat_upper :
    manuscriptNormV1_4SubstituteRat ≤ (-1719892378039867589719800831 / 500000000000000000000000000000) :=
  manuscriptNormV1_4SubstituteRat_interval.2.trans manuscriptNormV1_4_rounded_endpoints.2

def manuscriptNormV1_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV1_5SubstituteRat_interval :
    manuscriptNormV1_5SubstituteRat ∈ Set.Icc manuscriptNormV1_5Interval.1 manuscriptNormV1_5Interval.2 := by
  simpa only [manuscriptNormV1_5SubstituteRat, manuscriptNormV1_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num))

private theorem manuscriptNormV1_5SubstituteRat_upper :
    manuscriptNormV1_5SubstituteRat ≤ (1037754029533411800046178233 / 250000000000000000000000000000) :=
  manuscriptNormV1_5SubstituteRat_interval.2.trans manuscriptNormV1_5_rounded_endpoints.2

def manuscriptNormV1_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093)

private theorem manuscriptNormV1_6SubstituteRat_interval :
    manuscriptNormV1_6SubstituteRat ∈ Set.Icc manuscriptNormV1_6Interval.1 manuscriptNormV1_6Interval.2 := by
  simpa only [manuscriptNormV1_6SubstituteRat, manuscriptNormV1_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093) (by norm_num))

private theorem manuscriptNormV1_6SubstituteRat_upper :
    manuscriptNormV1_6SubstituteRat ≤ (1037754029533411800046178233 / 250000000000000000000000000000) :=
  manuscriptNormV1_6SubstituteRat_interval.2.trans manuscriptNormV1_6_rounded_endpoints.2

def manuscriptNormV1_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233)

private theorem manuscriptNormV1_7SubstituteRat_interval :
    manuscriptNormV1_7SubstituteRat ∈ Set.Icc manuscriptNormV1_7Interval.1 manuscriptNormV1_7Interval.2 := by
  simpa only [manuscriptNormV1_7SubstituteRat, manuscriptNormV1_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233) (by norm_num))

private theorem manuscriptNormV1_7SubstituteRat_upper :
    manuscriptNormV1_7SubstituteRat ≤ (1683260885525636238575254391 / 250000000000000000000000000000) :=
  manuscriptNormV1_7SubstituteRat_interval.2.trans manuscriptNormV1_7_rounded_endpoints.2

def manuscriptNormV1_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV1_8SubstituteRat_interval :
    manuscriptNormV1_8SubstituteRat ∈ Set.Icc manuscriptNormV1_8Interval.1 manuscriptNormV1_8Interval.2 := by
  simpa only [manuscriptNormV1_8SubstituteRat, manuscriptNormV1_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num))

private theorem manuscriptNormV1_8SubstituteRat_upper :
    manuscriptNormV1_8SubstituteRat ≤ (1683260885525636238575254391 / 250000000000000000000000000000) :=
  manuscriptNormV1_8SubstituteRat_interval.2.trans manuscriptNormV1_8_rounded_endpoints.2

def manuscriptNormV1_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599)

private theorem manuscriptNormV1_9SubstituteRat_interval :
    manuscriptNormV1_9SubstituteRat ∈ Set.Icc manuscriptNormV1_9Interval.1 manuscriptNormV1_9Interval.2 := by
  simpa only [manuscriptNormV1_9SubstituteRat, manuscriptNormV1_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599) (by norm_num))

private theorem manuscriptNormV1_9SubstituteRat_upper :
    manuscriptNormV1_9SubstituteRat ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) :=
  manuscriptNormV1_9SubstituteRat_interval.2.trans manuscriptNormV1_9_rounded_endpoints.2

def manuscriptNormV1_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV1_10SubstituteRat_interval :
    manuscriptNormV1_10SubstituteRat ∈ Set.Icc manuscriptNormV1_10Interval.1 manuscriptNormV1_10Interval.2 := by
  simpa only [manuscriptNormV1_10SubstituteRat, manuscriptNormV1_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num))

private theorem manuscriptNormV1_10SubstituteRat_upper :
    manuscriptNormV1_10SubstituteRat ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) :=
  manuscriptNormV1_10SubstituteRat_interval.2.trans manuscriptNormV1_10_rounded_endpoints.2

def manuscriptNormV1_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV1_11SubstituteRat_interval :
    manuscriptNormV1_11SubstituteRat ∈ Set.Icc manuscriptNormV1_11Interval.1 manuscriptNormV1_11Interval.2 := by
  simpa only [manuscriptNormV1_11SubstituteRat, manuscriptNormV1_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num))

private theorem manuscriptNormV1_11SubstituteRat_upper :
    manuscriptNormV1_11SubstituteRat ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) :=
  manuscriptNormV1_11SubstituteRat_interval.2.trans manuscriptNormV1_11_rounded_endpoints.2

def manuscriptNormV1_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV1_12SubstituteRat_interval :
    manuscriptNormV1_12SubstituteRat ∈ Set.Icc manuscriptNormV1_12Interval.1 manuscriptNormV1_12Interval.2 := by
  simpa only [manuscriptNormV1_12SubstituteRat, manuscriptNormV1_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num))

private theorem manuscriptNormV1_12SubstituteRat_upper :
    manuscriptNormV1_12SubstituteRat ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) :=
  manuscriptNormV1_12SubstituteRat_interval.2.trans manuscriptNormV1_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow1 : ℚ :=
  manuscriptNormV1_0SubstituteRat +
    manuscriptNormV1_1SubstituteRat +
    manuscriptNormV1_2SubstituteRat +
    manuscriptNormV1_3SubstituteRat +
    manuscriptNormV1_4SubstituteRat +
    manuscriptNormV1_5SubstituteRat +
    manuscriptNormV1_6SubstituteRat +
    manuscriptNormV1_7SubstituteRat +
    manuscriptNormV1_8SubstituteRat +
    manuscriptNormV1_9SubstituteRat +
    manuscriptNormV1_10SubstituteRat +
    manuscriptNormV1_11SubstituteRat +
    manuscriptNormV1_12SubstituteRat

theorem manuscriptNormVSubstituteRow1_upper : manuscriptNormVSubstituteRow1 ≤ (9497051844214097750258868783 / 250000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow1
  linarith only [manuscriptNormV1_0SubstituteRat_upper,
    manuscriptNormV1_1SubstituteRat_upper,
    manuscriptNormV1_2SubstituteRat_upper,
    manuscriptNormV1_3SubstituteRat_upper,
    manuscriptNormV1_4SubstituteRat_upper,
    manuscriptNormV1_5SubstituteRat_upper,
    manuscriptNormV1_6SubstituteRat_upper,
    manuscriptNormV1_7SubstituteRat_upper,
    manuscriptNormV1_8SubstituteRat_upper,
    manuscriptNormV1_9SubstituteRat_upper,
    manuscriptNormV1_10SubstituteRat_upper,
    manuscriptNormV1_11SubstituteRat_upper,
    manuscriptNormV1_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV1_0SubstituteRat_composition_error :
    |manuscriptNormV1_0Term - (manuscriptNormV1_0SubstituteRat : ℝ)| ≤ (((285565383 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_0SubstituteRat ∈ Set.Icc manuscriptNormV1_0Interval.1 manuscriptNormV1_0Interval.2 := by
    simpa only [manuscriptNormV1_0SubstituteRat, manuscriptNormV1_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_0Interval.1 manuscriptNormV1_0Interval.2 manuscriptNormV1_0SubstituteRat
    (9885502844684175872275224267 / 1000000000000000000000000000000) (9885502844684175874559747331 / 1000000000000000000000000000000) manuscriptNormV1_0Term
    manuscriptNormV1_0_exact_interval hq manuscriptNormV1_0_rounded_endpoints.1 manuscriptNormV1_0_rounded_endpoints.2
  have hw : ((9885502844684175874559747331 / 1000000000000000000000000000000) - (9885502844684175872275224267 / 1000000000000000000000000000000) : ℚ) = (285565383 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_1SubstituteRat_composition_error :
    |manuscriptNormV1_1Term - (manuscriptNormV1_1SubstituteRat : ℝ)| ≤ (((267632439 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_1SubstituteRat ∈ Set.Icc manuscriptNormV1_1Interval.1 manuscriptNormV1_1Interval.2 := by
    simpa only [manuscriptNormV1_1SubstituteRat, manuscriptNormV1_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_1Interval.1 manuscriptNormV1_1Interval.2 manuscriptNormV1_1SubstituteRat
    (1009069430608399715799384979 / 200000000000000000000000000000) (5045347153041998580067454651 / 1000000000000000000000000000000) manuscriptNormV1_1Term
    manuscriptNormV1_1_exact_interval hq manuscriptNormV1_1_rounded_endpoints.1 manuscriptNormV1_1_rounded_endpoints.2
  have hw : ((5045347153041998580067454651 / 1000000000000000000000000000000) - (1009069430608399715799384979 / 200000000000000000000000000000) : ℚ) = (267632439 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_2SubstituteRat_composition_error :
    |manuscriptNormV1_2Term - (manuscriptNormV1_2SubstituteRat : ℝ)| ≤ (((76521359 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_2SubstituteRat ∈ Set.Icc manuscriptNormV1_2Interval.1 manuscriptNormV1_2Interval.2 := by
    simpa only [manuscriptNormV1_2SubstituteRat, manuscriptNormV1_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_2Interval.1 manuscriptNormV1_2Interval.2 manuscriptNormV1_2SubstituteRat
    (-346946418840094216990697913 / 500000000000000000000000000000) (-693892837680188433904874467 / 1000000000000000000000000000000) manuscriptNormV1_2Term
    manuscriptNormV1_2_exact_interval hq manuscriptNormV1_2_rounded_endpoints.1 manuscriptNormV1_2_rounded_endpoints.2
  have hw : ((-693892837680188433904874467 / 1000000000000000000000000000000) - (-346946418840094216990697913 / 500000000000000000000000000000) : ℚ) = (76521359 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_3SubstituteRat_composition_error :
    |manuscriptNormV1_3Term - (manuscriptNormV1_3SubstituteRat : ℝ)| ≤ (((18682129 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_3SubstituteRat ∈ Set.Icc manuscriptNormV1_3Interval.1 manuscriptNormV1_3Interval.2 := by
    simpa only [manuscriptNormV1_3SubstituteRat, manuscriptNormV1_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_3Interval.1 manuscriptNormV1_3Interval.2 manuscriptNormV1_3SubstituteRat
    (284646908465717807696825671 / 200000000000000000000000000000) (1423234542328589038633585387 / 1000000000000000000000000000000) manuscriptNormV1_3Term
    manuscriptNormV1_3_exact_interval hq manuscriptNormV1_3_rounded_endpoints.1 manuscriptNormV1_3_rounded_endpoints.2
  have hw : ((1423234542328589038633585387 / 1000000000000000000000000000000) - (284646908465717807696825671 / 200000000000000000000000000000) : ℚ) = (18682129 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_4SubstituteRat_composition_error :
    |manuscriptNormV1_4Term - (manuscriptNormV1_4SubstituteRat : ℝ)| ≤ (((45999499 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_4SubstituteRat ∈ Set.Icc manuscriptNormV1_4Interval.1 manuscriptNormV1_4Interval.2 := by
    simpa only [manuscriptNormV1_4SubstituteRat, manuscriptNormV1_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_4Interval.1 manuscriptNormV1_4Interval.2 manuscriptNormV1_4SubstituteRat
    (-1719892378039867589903798827 / 500000000000000000000000000000) (-1719892378039867589719800831 / 500000000000000000000000000000) manuscriptNormV1_4Term
    manuscriptNormV1_4_exact_interval hq manuscriptNormV1_4_rounded_endpoints.1 manuscriptNormV1_4_rounded_endpoints.2
  have hw : ((-1719892378039867589719800831 / 500000000000000000000000000000) - (-1719892378039867589903798827 / 500000000000000000000000000000) : ℚ) = (45999499 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_5SubstituteRat_composition_error :
    |manuscriptNormV1_5Term - (manuscriptNormV1_5SubstituteRat : ℝ)| ≤ (((77560278431 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_5SubstituteRat ∈ Set.Icc manuscriptNormV1_5Interval.1 manuscriptNormV1_5Interval.2 := by
    simpa only [manuscriptNormV1_5SubstituteRat, manuscriptNormV1_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_5Interval.1 manuscriptNormV1_5Interval.2 manuscriptNormV1_5SubstituteRat
    (518877014766705861242949901 / 125000000000000000000000000000) (1037754029533411800046178233 / 250000000000000000000000000000) manuscriptNormV1_5Term
    manuscriptNormV1_5_exact_interval hq manuscriptNormV1_5_rounded_endpoints.1 manuscriptNormV1_5_rounded_endpoints.2
  have hw : ((1037754029533411800046178233 / 250000000000000000000000000000) - (518877014766705861242949901 / 125000000000000000000000000000) : ℚ) = (77560278431 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_6SubstituteRat_composition_error :
    |manuscriptNormV1_6Term - (manuscriptNormV1_6SubstituteRat : ℝ)| ≤ (((77560278431 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_6SubstituteRat ∈ Set.Icc manuscriptNormV1_6Interval.1 manuscriptNormV1_6Interval.2 := by
    simpa only [manuscriptNormV1_6SubstituteRat, manuscriptNormV1_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_6Interval.1 manuscriptNormV1_6Interval.2 manuscriptNormV1_6SubstituteRat
    (518877014766705861242949901 / 125000000000000000000000000000) (1037754029533411800046178233 / 250000000000000000000000000000) manuscriptNormV1_6Term
    manuscriptNormV1_6_exact_interval hq manuscriptNormV1_6_rounded_endpoints.1 manuscriptNormV1_6_rounded_endpoints.2
  have hw : ((1037754029533411800046178233 / 250000000000000000000000000000) - (518877014766705861242949901 / 125000000000000000000000000000) : ℚ) = (77560278431 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_7SubstituteRat_composition_error :
    |manuscriptNormV1_7Term - (manuscriptNormV1_7SubstituteRat : ℝ)| ≤ (((121798628223 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_7SubstituteRat ∈ Set.Icc manuscriptNormV1_7Interval.1 manuscriptNormV1_7Interval.2 := by
    simpa only [manuscriptNormV1_7SubstituteRat, manuscriptNormV1_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_7Interval.1 manuscriptNormV1_7Interval.2 manuscriptNormV1_7SubstituteRat
    (3366521771051272355351880559 / 500000000000000000000000000000) (1683260885525636238575254391 / 250000000000000000000000000000) manuscriptNormV1_7Term
    manuscriptNormV1_7_exact_interval hq manuscriptNormV1_7_rounded_endpoints.1 manuscriptNormV1_7_rounded_endpoints.2
  have hw : ((1683260885525636238575254391 / 250000000000000000000000000000) - (3366521771051272355351880559 / 500000000000000000000000000000) : ℚ) = (121798628223 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_8SubstituteRat_composition_error :
    |manuscriptNormV1_8Term - (manuscriptNormV1_8SubstituteRat : ℝ)| ≤ (((121798628223 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_8SubstituteRat ∈ Set.Icc manuscriptNormV1_8Interval.1 manuscriptNormV1_8Interval.2 := by
    simpa only [manuscriptNormV1_8SubstituteRat, manuscriptNormV1_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_8Interval.1 manuscriptNormV1_8Interval.2 manuscriptNormV1_8SubstituteRat
    (3366521771051272355351880559 / 500000000000000000000000000000) (1683260885525636238575254391 / 250000000000000000000000000000) manuscriptNormV1_8Term
    manuscriptNormV1_8_exact_interval hq manuscriptNormV1_8_rounded_endpoints.1 manuscriptNormV1_8_rounded_endpoints.2
  have hw : ((1683260885525636238575254391 / 250000000000000000000000000000) - (3366521771051272355351880559 / 500000000000000000000000000000) : ℚ) = (121798628223 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_9SubstituteRat_composition_error :
    |manuscriptNormV1_9Term - (manuscriptNormV1_9SubstituteRat : ℝ)| ≤ (((24030658553 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_9SubstituteRat ∈ Set.Icc manuscriptNormV1_9Interval.1 manuscriptNormV1_9Interval.2 := by
    simpa only [manuscriptNormV1_9SubstituteRat, manuscriptNormV1_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_9Interval.1 manuscriptNormV1_9Interval.2 manuscriptNormV1_9SubstituteRat
    (-1512993449261219836137063493 / 1000000000000000000000000000000) (-1512993449261219740014429281 / 1000000000000000000000000000000) manuscriptNormV1_9Term
    manuscriptNormV1_9_exact_interval hq manuscriptNormV1_9_rounded_endpoints.1 manuscriptNormV1_9_rounded_endpoints.2
  have hw : ((-1512993449261219740014429281 / 1000000000000000000000000000000) - (-1512993449261219836137063493 / 1000000000000000000000000000000) : ℚ) = (24030658553 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_10SubstituteRat_composition_error :
    |manuscriptNormV1_10Term - (manuscriptNormV1_10SubstituteRat : ℝ)| ≤ (((24030658553 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_10SubstituteRat ∈ Set.Icc manuscriptNormV1_10Interval.1 manuscriptNormV1_10Interval.2 := by
    simpa only [manuscriptNormV1_10SubstituteRat, manuscriptNormV1_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_10Interval.1 manuscriptNormV1_10Interval.2 manuscriptNormV1_10SubstituteRat
    (-1512993449261219836137063493 / 1000000000000000000000000000000) (-1512993449261219740014429281 / 1000000000000000000000000000000) manuscriptNormV1_10Term
    manuscriptNormV1_10_exact_interval hq manuscriptNormV1_10_rounded_endpoints.1 manuscriptNormV1_10_rounded_endpoints.2
  have hw : ((-1512993449261219740014429281 / 1000000000000000000000000000000) - (-1512993449261219836137063493 / 1000000000000000000000000000000) : ℚ) = (24030658553 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_11SubstituteRat_composition_error :
    |manuscriptNormV1_11Term - (manuscriptNormV1_11SubstituteRat : ℝ)| ≤ (((175229584383 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_11SubstituteRat ∈ Set.Icc manuscriptNormV1_11Interval.1 manuscriptNormV1_11Interval.2 := by
    simpa only [manuscriptNormV1_11SubstituteRat, manuscriptNormV1_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_11Interval.1 manuscriptNormV1_11Interval.2 manuscriptNormV1_11SubstituteRat
    (878208501076450742714674087 / 250000000000000000000000000000) (3512834004305803146088280731 / 1000000000000000000000000000000) manuscriptNormV1_11Term
    manuscriptNormV1_11_exact_interval hq manuscriptNormV1_11_rounded_endpoints.1 manuscriptNormV1_11_rounded_endpoints.2
  have hw : ((3512834004305803146088280731 / 1000000000000000000000000000000) - (878208501076450742714674087 / 250000000000000000000000000000) : ℚ) = (175229584383 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV1_12SubstituteRat_composition_error :
    |manuscriptNormV1_12Term - (manuscriptNormV1_12SubstituteRat : ℝ)| ≤ (((175229584383 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV1_12SubstituteRat ∈ Set.Icc manuscriptNormV1_12Interval.1 manuscriptNormV1_12Interval.2 := by
    simpa only [manuscriptNormV1_12SubstituteRat, manuscriptNormV1_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV1_12Interval.1 manuscriptNormV1_12Interval.2 manuscriptNormV1_12SubstituteRat
    (878208501076450742714674087 / 250000000000000000000000000000) (3512834004305803146088280731 / 1000000000000000000000000000000) manuscriptNormV1_12Term
    manuscriptNormV1_12_exact_interval hq manuscriptNormV1_12_rounded_endpoints.1 manuscriptNormV1_12_rounded_endpoints.2
  have hw : ((3512834004305803146088280731 / 1000000000000000000000000000000) - (878208501076450742714674087 / 250000000000000000000000000000) : ℚ) = (175229584383 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow1_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 1 (0, 0)) - (manuscriptNormVSubstituteRow1 : ℝ)| ≤ (((1654330204733 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV1_0SubstituteRat_composition_error
  have h1 := manuscriptNormV1_1SubstituteRat_composition_error
  have h2 := manuscriptNormV1_2SubstituteRat_composition_error
  have h3 := manuscriptNormV1_3SubstituteRat_composition_error
  have h4 := manuscriptNormV1_4SubstituteRat_composition_error
  have h5 := manuscriptNormV1_5SubstituteRat_composition_error
  have h6 := manuscriptNormV1_6SubstituteRat_composition_error
  have h7 := manuscriptNormV1_7SubstituteRat_composition_error
  have h8 := manuscriptNormV1_8SubstituteRat_composition_error
  have h9 := manuscriptNormV1_9SubstituteRat_composition_error
  have h10 := manuscriptNormV1_10SubstituteRat_composition_error
  have h11 := manuscriptNormV1_11SubstituteRat_composition_error
  have h12 := manuscriptNormV1_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV1_0Term + (manuscriptNormV1_1Term + (manuscriptNormV1_2Term + (manuscriptNormV1_3Term + (manuscriptNormV1_4Term + (manuscriptNormV1_5Term + (manuscriptNormV1_6Term + (manuscriptNormV1_7Term + (manuscriptNormV1_8Term + (manuscriptNormV1_9Term + (manuscriptNormV1_10Term + (manuscriptNormV1_11Term + (manuscriptNormV1_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow1 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow1
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

def manuscriptNormV1_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV1_0RoundedSubstituteRat_error :
    |(manuscriptNormV1_0SubstituteRat : ℝ) - (manuscriptNormV1_0RoundedSubstituteRat : ℝ)| ≤
      (((33830875019341 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-33830875019341 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((33830875019341 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1)

private theorem manuscriptNormV1_1RoundedSubstituteRat_error :
    |(manuscriptNormV1_1SubstituteRat : ℝ) - (manuscriptNormV1_1RoundedSubstituteRat : ℝ)| ≤
      (((4954323640561 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4954323640561 / 2500000000000000) (0 / 1) (-8) (0) (614656 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-4954323640561 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((4954323640561 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV1_2RoundedSubstituteRat_error :
    |(manuscriptNormV1_2SubstituteRat : ℝ) - (manuscriptNormV1_2RoundedSubstituteRat : ℝ)| ≤
      (((2832812887869 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2832812887869 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((2832812887869 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV1_3RoundedSubstituteRat_error :
    |(manuscriptNormV1_3SubstituteRat : ℝ) - (manuscriptNormV1_3RoundedSubstituteRat : ℝ)| ≤
      (((5489604834427 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((5489604834427 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((5489604834427 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV1_4RoundedSubstituteRat_error :
    |(manuscriptNormV1_4SubstituteRat : ℝ) - (manuscriptNormV1_4RoundedSubstituteRat : ℝ)| ≤
      (((25860054013467 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-25860054013467 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((25860054013467 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV1_5RoundedSubstituteRat_error :
    |(manuscriptNormV1_5SubstituteRat : ℝ) - (manuscriptNormV1_5RoundedSubstituteRat : ℝ)| ≤
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num) (by norm_num)
  have hw : |(((-30314387010667 / 5000000000000000) : ℚ) : ℝ)| + |(((-1337165747419 / 156250000000000) : ℚ) : ℝ)| =
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093)

private theorem manuscriptNormV1_6RoundedSubstituteRat_error :
    |(manuscriptNormV1_6SubstituteRat : ℝ) - (manuscriptNormV1_6RoundedSubstituteRat : ℝ)| ≤
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093) (by norm_num) (by norm_num)
  have hw : |(((-30314387010667 / 5000000000000000) : ℚ) : ℝ)| + |(((1337165747419 / 156250000000000) : ℚ) : ℝ)| =
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233)

private theorem manuscriptNormV1_7RoundedSubstituteRat_error :
    |(manuscriptNormV1_7SubstituteRat : ℝ) - (manuscriptNormV1_7RoundedSubstituteRat : ℝ)| ≤
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233) (by norm_num) (by norm_num)
  have hw : |(((17439989085201 / 2500000000000000) : ℚ) : ℝ)| + |(((-33597567865583 / 5000000000000000) : ℚ) : ℝ)| =
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV1_8RoundedSubstituteRat_error :
    |(manuscriptNormV1_8SubstituteRat : ℝ) - (manuscriptNormV1_8RoundedSubstituteRat : ℝ)| ≤
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num) (by norm_num)
  have hw : |(((17439989085201 / 2500000000000000) : ℚ) : ℝ)| + |(((33597567865583 / 5000000000000000) : ℚ) : ℝ)| =
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599)

private theorem manuscriptNormV1_9RoundedSubstituteRat_error :
    |(manuscriptNormV1_9SubstituteRat : ℝ) - (manuscriptNormV1_9RoundedSubstituteRat : ℝ)| ≤
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599) (by norm_num) (by norm_num)
  have hw : |(((7449346641701 / 5000000000000000) : ℚ) : ℝ)| + |(((13257332116537 / 5000000000000000) : ℚ) : ℝ)| =
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV1_10RoundedSubstituteRat_error :
    |(manuscriptNormV1_10SubstituteRat : ℝ) - (manuscriptNormV1_10RoundedSubstituteRat : ℝ)| ≤
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num) (by norm_num)
  have hw : |(((7449346641701 / 5000000000000000) : ℚ) : ℝ)| + |(((-13257332116537 / 5000000000000000) : ℚ) : ℝ)| =
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV1_11RoundedSubstituteRat_error :
    |(manuscriptNormV1_11SubstituteRat : ℝ) - (manuscriptNormV1_11RoundedSubstituteRat : ℝ)| ≤
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077) (by norm_num) (by norm_num)
  have hw : |(((-4574556807003 / 10000000000000000) : ℚ) : ℝ)| + |(((-48335809895519 / 10000000000000000) : ℚ) : ℝ)| =
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV1_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV1_12RoundedSubstituteRat_error :
    |(manuscriptNormV1_12SubstituteRat : ℝ) - (manuscriptNormV1_12RoundedSubstituteRat : ℝ)| ≤
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077) (by norm_num) (by norm_num)
  have hw : |(((-4574556807003 / 10000000000000000) : ℚ) : ℝ)| + |(((48335809895519 / 10000000000000000) : ℚ) : ℝ)| =
      (((26455183351261 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow1 : ℚ :=
  manuscriptNormV1_0RoundedSubstituteRat +
    manuscriptNormV1_1RoundedSubstituteRat +
    manuscriptNormV1_2RoundedSubstituteRat +
    manuscriptNormV1_3RoundedSubstituteRat +
    manuscriptNormV1_4RoundedSubstituteRat +
    manuscriptNormV1_5RoundedSubstituteRat +
    manuscriptNormV1_6RoundedSubstituteRat +
    manuscriptNormV1_7RoundedSubstituteRat +
    manuscriptNormV1_8RoundedSubstituteRat +
    manuscriptNormV1_9RoundedSubstituteRat +
    manuscriptNormV1_10RoundedSubstituteRat +
    manuscriptNormV1_11RoundedSubstituteRat +
    manuscriptNormV1_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow1_error :
    |(manuscriptNormVSubstituteRow1 : ℝ) - (manuscriptNormVRoundedSubstituteRow1 : ℝ)| ≤
      (((11593265247641 / 125000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV1_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV1_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV1_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV1_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV1_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV1_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV1_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV1_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV1_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV1_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV1_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV1_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV1_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow1 manuscriptNormVRoundedSubstituteRow1
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

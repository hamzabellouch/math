import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup034
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup035
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup036
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup037
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup038
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV8_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV8_0SubstituteRat_interval :
    manuscriptNormV8_0SubstituteRat ∈ Set.Icc manuscriptNormV8_0Interval.1 manuscriptNormV8_0Interval.2 := by
  simpa only [manuscriptNormV8_0SubstituteRat, manuscriptNormV8_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num))

private theorem manuscriptNormV8_0SubstituteRat_upper :
    manuscriptNormV8_0SubstituteRat ≤ (3858078394234498723893081383 / 200000000000000000000000000000) :=
  manuscriptNormV8_0SubstituteRat_interval.2.trans manuscriptNormV8_0_rounded_endpoints.2

def manuscriptNormV8_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV8_1SubstituteRat_interval :
    manuscriptNormV8_1SubstituteRat ∈ Set.Icc manuscriptNormV8_1Interval.1 manuscriptNormV8_1Interval.2 := by
  simpa only [manuscriptNormV8_1SubstituteRat, manuscriptNormV8_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num))

private theorem manuscriptNormV8_1SubstituteRat_upper :
    manuscriptNormV8_1SubstituteRat ≤ (1683260885525636238575254391 / 250000000000000000000000000000) :=
  manuscriptNormV8_1SubstituteRat_interval.2.trans manuscriptNormV8_1_rounded_endpoints.2

def manuscriptNormV8_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV8_2SubstituteRat_interval :
    manuscriptNormV8_2SubstituteRat ∈ Set.Icc manuscriptNormV8_2Interval.1 manuscriptNormV8_2Interval.2 := by
  simpa only [manuscriptNormV8_2SubstituteRat, manuscriptNormV8_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num))

private theorem manuscriptNormV8_2SubstituteRat_upper :
    manuscriptNormV8_2SubstituteRat ≤ (-400638762523047475177650967 / 250000000000000000000000000000) :=
  manuscriptNormV8_2SubstituteRat_interval.2.trans manuscriptNormV8_2_rounded_endpoints.2

def manuscriptNormV8_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV8_3SubstituteRat_interval :
    manuscriptNormV8_3SubstituteRat ∈ Set.Icc manuscriptNormV8_3Interval.1 manuscriptNormV8_3Interval.2 := by
  simpa only [manuscriptNormV8_3SubstituteRat, manuscriptNormV8_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num))

private theorem manuscriptNormV8_3SubstituteRat_upper :
    manuscriptNormV8_3SubstituteRat ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) :=
  manuscriptNormV8_3SubstituteRat_interval.2.trans manuscriptNormV8_3_rounded_endpoints.2

def manuscriptNormV8_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV8_4SubstituteRat_interval :
    manuscriptNormV8_4SubstituteRat ∈ Set.Icc manuscriptNormV8_4Interval.1 manuscriptNormV8_4Interval.2 := by
  simpa only [manuscriptNormV8_4SubstituteRat, manuscriptNormV8_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num))

private theorem manuscriptNormV8_4SubstituteRat_upper :
    manuscriptNormV8_4SubstituteRat ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) :=
  manuscriptNormV8_4SubstituteRat_interval.2.trans manuscriptNormV8_4_rounded_endpoints.2

def manuscriptNormV8_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV8_5SubstituteRat_interval :
    manuscriptNormV8_5SubstituteRat ∈ Set.Icc manuscriptNormV8_5Interval.1 manuscriptNormV8_5Interval.2 := by
  simpa only [manuscriptNormV8_5SubstituteRat, manuscriptNormV8_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_5SubstituteRat_upper :
    manuscriptNormV8_5SubstituteRat ≤ (1161500178636992697332422467 / 125000000000000000000000000000) :=
  manuscriptNormV8_5SubstituteRat_interval.2.trans manuscriptNormV8_5_rounded_endpoints.2

def manuscriptNormV8_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV8_6SubstituteRat_interval :
    manuscriptNormV8_6SubstituteRat ∈ Set.Icc manuscriptNormV8_6Interval.1 manuscriptNormV8_6Interval.2 := by
  simpa only [manuscriptNormV8_6SubstituteRat, manuscriptNormV8_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_6SubstituteRat_upper :
    manuscriptNormV8_6SubstituteRat ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) :=
  manuscriptNormV8_6SubstituteRat_interval.2.trans manuscriptNormV8_6_rounded_endpoints.2

def manuscriptNormV8_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1)

private theorem manuscriptNormV8_7SubstituteRat_interval :
    manuscriptNormV8_7SubstituteRat ∈ Set.Icc manuscriptNormV8_7Interval.1 manuscriptNormV8_7Interval.2 := by
  simpa only [manuscriptNormV8_7SubstituteRat, manuscriptNormV8_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_7SubstituteRat_upper :
    manuscriptNormV8_7SubstituteRat ≤ (4913756824386368134848479063 / 62500000000000000000000000000) :=
  manuscriptNormV8_7SubstituteRat_interval.2.trans manuscriptNormV8_7_rounded_endpoints.2

def manuscriptNormV8_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1)

private theorem manuscriptNormV8_8SubstituteRat_interval :
    manuscriptNormV8_8SubstituteRat ∈ Set.Icc manuscriptNormV8_8Interval.1 manuscriptNormV8_8Interval.2 := by
  simpa only [manuscriptNormV8_8SubstituteRat, manuscriptNormV8_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_8SubstituteRat_upper :
    manuscriptNormV8_8SubstituteRat ≤ (-16432545326496599533657089 / 15625000000000000000000000000) :=
  manuscriptNormV8_8SubstituteRat_interval.2.trans manuscriptNormV8_8_rounded_endpoints.2

def manuscriptNormV8_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV8_9SubstituteRat_interval :
    manuscriptNormV8_9SubstituteRat ∈ Set.Icc manuscriptNormV8_9Interval.1 manuscriptNormV8_9Interval.2 := by
  simpa only [manuscriptNormV8_9SubstituteRat, manuscriptNormV8_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_9SubstituteRat_upper :
    manuscriptNormV8_9SubstituteRat ≤ (-735139122654920217587852529 / 100000000000000000000000000000) :=
  manuscriptNormV8_9SubstituteRat_interval.2.trans manuscriptNormV8_9_rounded_endpoints.2

def manuscriptNormV8_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV8_10SubstituteRat_interval :
    manuscriptNormV8_10SubstituteRat ∈ Set.Icc manuscriptNormV8_10Interval.1 manuscriptNormV8_10Interval.2 := by
  simpa only [manuscriptNormV8_10SubstituteRat, manuscriptNormV8_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_10SubstituteRat_upper :
    manuscriptNormV8_10SubstituteRat ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) :=
  manuscriptNormV8_10SubstituteRat_interval.2.trans manuscriptNormV8_10_rounded_endpoints.2

def manuscriptNormV8_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV8_11SubstituteRat_interval :
    manuscriptNormV8_11SubstituteRat ∈ Set.Icc manuscriptNormV8_11Interval.1 manuscriptNormV8_11Interval.2 := by
  simpa only [manuscriptNormV8_11SubstituteRat, manuscriptNormV8_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_11SubstituteRat_upper :
    manuscriptNormV8_11SubstituteRat ≤ (16020904669330418666468974703 / 500000000000000000000000000000) :=
  manuscriptNormV8_11SubstituteRat_interval.2.trans manuscriptNormV8_11_rounded_endpoints.2

def manuscriptNormV8_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV8_12SubstituteRat_interval :
    manuscriptNormV8_12SubstituteRat ∈ Set.Icc manuscriptNormV8_12Interval.1 manuscriptNormV8_12Interval.2 := by
  simpa only [manuscriptNormV8_12SubstituteRat, manuscriptNormV8_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV8_12SubstituteRat_upper :
    manuscriptNormV8_12SubstituteRat ≤ (11416234618393557261110141487 / 1000000000000000000000000000000) :=
  manuscriptNormV8_12SubstituteRat_interval.2.trans manuscriptNormV8_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow8 : ℚ :=
  manuscriptNormV8_0SubstituteRat +
    manuscriptNormV8_1SubstituteRat +
    manuscriptNormV8_2SubstituteRat +
    manuscriptNormV8_3SubstituteRat +
    manuscriptNormV8_4SubstituteRat +
    manuscriptNormV8_5SubstituteRat +
    manuscriptNormV8_6SubstituteRat +
    manuscriptNormV8_7SubstituteRat +
    manuscriptNormV8_8SubstituteRat +
    manuscriptNormV8_9SubstituteRat +
    manuscriptNormV8_10SubstituteRat +
    manuscriptNormV8_11SubstituteRat +
    manuscriptNormV8_12SubstituteRat

theorem manuscriptNormVSubstituteRow8_upper : manuscriptNormVSubstituteRow8 ≤ (161045663394817546404515372521 / 1000000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow8
  linarith only [manuscriptNormV8_0SubstituteRat_upper,
    manuscriptNormV8_1SubstituteRat_upper,
    manuscriptNormV8_2SubstituteRat_upper,
    manuscriptNormV8_3SubstituteRat_upper,
    manuscriptNormV8_4SubstituteRat_upper,
    manuscriptNormV8_5SubstituteRat_upper,
    manuscriptNormV8_6SubstituteRat_upper,
    manuscriptNormV8_7SubstituteRat_upper,
    manuscriptNormV8_8SubstituteRat_upper,
    manuscriptNormV8_9SubstituteRat_upper,
    manuscriptNormV8_10SubstituteRat_upper,
    manuscriptNormV8_11SubstituteRat_upper,
    manuscriptNormV8_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV8_0SubstituteRat_composition_error :
    |manuscriptNormV8_0Term - (manuscriptNormV8_0SubstituteRat : ℝ)| ≤ (((831707907701 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_0SubstituteRat ∈ Set.Icc manuscriptNormV8_0Interval.1 manuscriptNormV8_0Interval.2 := by
    simpa only [manuscriptNormV8_0SubstituteRat, manuscriptNormV8_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_0Interval.1 manuscriptNormV8_0Interval.2 manuscriptNormV8_0SubstituteRat
    (9645195985586246393878749607 / 500000000000000000000000000000) (3858078394234498723893081383 / 200000000000000000000000000000) manuscriptNormV8_0Term
    manuscriptNormV8_0_exact_interval hq manuscriptNormV8_0_rounded_endpoints.1 manuscriptNormV8_0_rounded_endpoints.2
  have hw : ((3858078394234498723893081383 / 200000000000000000000000000000) - (9645195985586246393878749607 / 500000000000000000000000000000) : ℚ) = (831707907701 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_1SubstituteRat_composition_error :
    |manuscriptNormV8_1Term - (manuscriptNormV8_1SubstituteRat : ℝ)| ≤ (((121798628223 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_1SubstituteRat ∈ Set.Icc manuscriptNormV8_1Interval.1 manuscriptNormV8_1Interval.2 := by
    simpa only [manuscriptNormV8_1SubstituteRat, manuscriptNormV8_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_1Interval.1 manuscriptNormV8_1Interval.2 manuscriptNormV8_1SubstituteRat
    (3366521771051272355351880559 / 500000000000000000000000000000) (1683260885525636238575254391 / 250000000000000000000000000000) manuscriptNormV8_1Term
    manuscriptNormV8_1_exact_interval hq manuscriptNormV8_1_rounded_endpoints.1 manuscriptNormV8_1_rounded_endpoints.2
  have hw : ((1683260885525636238575254391 / 250000000000000000000000000000) - (3366521771051272355351880559 / 500000000000000000000000000000) : ℚ) = (121798628223 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_2SubstituteRat_composition_error :
    |manuscriptNormV8_2Term - (manuscriptNormV8_2SubstituteRat : ℝ)| ≤ (((69642682819 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_2SubstituteRat ∈ Set.Icc manuscriptNormV8_2Interval.1 manuscriptNormV8_2Interval.2 := by
    simpa only [manuscriptNormV8_2SubstituteRat, manuscriptNormV8_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_2Interval.1 manuscriptNormV8_2Interval.2 manuscriptNormV8_2SubstituteRat
    (-801277525046095019997984753 / 500000000000000000000000000000) (-400638762523047475177650967 / 250000000000000000000000000000) manuscriptNormV8_2Term
    manuscriptNormV8_2_exact_interval hq manuscriptNormV8_2_rounded_endpoints.1 manuscriptNormV8_2_rounded_endpoints.2
  have hw : ((-400638762523047475177650967 / 250000000000000000000000000000) - (-801277525046095019997984753 / 500000000000000000000000000000) : ℚ) = (69642682819 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_3SubstituteRat_composition_error :
    |manuscriptNormV8_3Term - (manuscriptNormV8_3SubstituteRat : ℝ)| ≤ (((33739522489 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_3SubstituteRat ∈ Set.Icc manuscriptNormV8_3Interval.1 manuscriptNormV8_3Interval.2 := by
    simpa only [manuscriptNormV8_3SubstituteRat, manuscriptNormV8_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_3Interval.1 manuscriptNormV8_3Interval.2 manuscriptNormV8_3SubstituteRat
    (3146180457411023770175562599 / 1000000000000000000000000000000) (3146180457411024040091742511 / 1000000000000000000000000000000) manuscriptNormV8_3Term
    manuscriptNormV8_3_exact_interval hq manuscriptNormV8_3_rounded_endpoints.1 manuscriptNormV8_3_rounded_endpoints.2
  have hw : ((3146180457411024040091742511 / 1000000000000000000000000000000) - (3146180457411023770175562599 / 1000000000000000000000000000000) : ℚ) = (33739522489 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_4SubstituteRat_composition_error :
    |manuscriptNormV8_4Term - (manuscriptNormV8_4SubstituteRat : ℝ)| ≤ (((79469162947 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_4SubstituteRat ∈ Set.Icc manuscriptNormV8_4Interval.1 manuscriptNormV8_4Interval.2 := by
    simpa only [manuscriptNormV8_4SubstituteRat, manuscriptNormV8_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_4Interval.1 manuscriptNormV8_4Interval.2 manuscriptNormV8_4SubstituteRat
    (-7439891480413310489970227707 / 1000000000000000000000000000000) (-7439891480413309854216924131 / 1000000000000000000000000000000) manuscriptNormV8_4Term
    manuscriptNormV8_4_exact_interval hq manuscriptNormV8_4_rounded_endpoints.1 manuscriptNormV8_4_rounded_endpoints.2
  have hw : ((-7439891480413309854216924131 / 1000000000000000000000000000000) - (-7439891480413310489970227707 / 1000000000000000000000000000000) : ℚ) = (79469162947 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_5SubstituteRat_composition_error :
    |manuscriptNormV8_5Term - (manuscriptNormV8_5SubstituteRat : ℝ)| ≤ (((2073054867 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_5SubstituteRat ∈ Set.Icc manuscriptNormV8_5Interval.1 manuscriptNormV8_5Interval.2 := by
    simpa only [manuscriptNormV8_5SubstituteRat, manuscriptNormV8_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_5Interval.1 manuscriptNormV8_5Interval.2 manuscriptNormV8_5SubstituteRat
    (9292001429095941576586324869 / 1000000000000000000000000000000) (1161500178636992697332422467 / 125000000000000000000000000000) manuscriptNormV8_5Term
    manuscriptNormV8_5_exact_interval hq manuscriptNormV8_5_rounded_endpoints.1 manuscriptNormV8_5_rounded_endpoints.2
  have hw : ((1161500178636992697332422467 / 125000000000000000000000000000) - (9292001429095941576586324869 / 1000000000000000000000000000000) : ℚ) = (2073054867 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_6SubstituteRat_composition_error :
    |manuscriptNormV8_6Term - (manuscriptNormV8_6SubstituteRat : ℝ)| ≤ (((3400535907 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_6SubstituteRat ∈ Set.Icc manuscriptNormV8_6Interval.1 manuscriptNormV8_6Interval.2 := by
    simpa only [manuscriptNormV8_6SubstituteRat, manuscriptNormV8_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_6Interval.1 manuscriptNormV8_6Interval.2 manuscriptNormV8_6SubstituteRat
    (2678148258356293550482966351 / 100000000000000000000000000000) (26781482583562935508230199417 / 1000000000000000000000000000000) manuscriptNormV8_6Term
    manuscriptNormV8_6_exact_interval hq manuscriptNormV8_6_rounded_endpoints.1 manuscriptNormV8_6_rounded_endpoints.2
  have hw : ((26781482583562935508230199417 / 1000000000000000000000000000000) - (2678148258356293550482966351 / 100000000000000000000000000000) : ℚ) = (3400535907 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_7SubstituteRat_composition_error :
    |manuscriptNormV8_7Term - (manuscriptNormV8_7SubstituteRat : ℝ)| ≤ (((7991690909 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_7SubstituteRat ∈ Set.Icc manuscriptNormV8_7Interval.1 manuscriptNormV8_7Interval.2 := by
    simpa only [manuscriptNormV8_7SubstituteRat, manuscriptNormV8_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_7Interval.1 manuscriptNormV8_7Interval.2 manuscriptNormV8_7SubstituteRat
    (7862010919018189014159228319 / 100000000000000000000000000000) (4913756824386368134848479063 / 62500000000000000000000000000) manuscriptNormV8_7Term
    manuscriptNormV8_7_exact_interval hq manuscriptNormV8_7_rounded_endpoints.1 manuscriptNormV8_7_rounded_endpoints.2
  have hw : ((4913756824386368134848479063 / 62500000000000000000000000000) - (7862010919018189014159228319 / 100000000000000000000000000000) : ℚ) = (7991690909 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_8SubstituteRat_composition_error :
    |manuscriptNormV8_8Term - (manuscriptNormV8_8SubstituteRat : ℝ)| ≤ (((23938011 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_8SubstituteRat ∈ Set.Icc manuscriptNormV8_8Interval.1 manuscriptNormV8_8Interval.2 := by
    simpa only [manuscriptNormV8_8SubstituteRat, manuscriptNormV8_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_8Interval.1 manuscriptNormV8_8Interval.2 manuscriptNormV8_8SubstituteRat
    (-1051682900895782370273743751 / 1000000000000000000000000000000) (-16432545326496599533657089 / 15625000000000000000000000000) manuscriptNormV8_8Term
    manuscriptNormV8_8_exact_interval hq manuscriptNormV8_8_rounded_endpoints.1 manuscriptNormV8_8_rounded_endpoints.2
  have hw : ((-16432545326496599533657089 / 15625000000000000000000000000) - (-1051682900895782370273743751 / 1000000000000000000000000000000) : ℚ) = (23938011 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_9SubstituteRat_composition_error :
    |manuscriptNormV8_9Term - (manuscriptNormV8_9SubstituteRat : ℝ)| ≤ (((758813281 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_9SubstituteRat ∈ Set.Icc manuscriptNormV8_9Interval.1 manuscriptNormV8_9Interval.2 := by
    simpa only [manuscriptNormV8_9SubstituteRat, manuscriptNormV8_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_9Interval.1 manuscriptNormV8_9Interval.2 manuscriptNormV8_9SubstituteRat
    (-1837847806637300544349037963 / 250000000000000000000000000000) (-735139122654920217587852529 / 100000000000000000000000000000) manuscriptNormV8_9Term
    manuscriptNormV8_9_exact_interval hq manuscriptNormV8_9_rounded_endpoints.1 manuscriptNormV8_9_rounded_endpoints.2
  have hw : ((-735139122654920217587852529 / 100000000000000000000000000000) - (-1837847806637300544349037963 / 250000000000000000000000000000) : ℚ) = (758813281 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_10SubstituteRat_composition_error :
    |manuscriptNormV8_10Term - (manuscriptNormV8_10SubstituteRat : ℝ)| ≤ (((480735149 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_10SubstituteRat ∈ Set.Icc manuscriptNormV8_10Interval.1 manuscriptNormV8_10Interval.2 := by
    simpa only [manuscriptNormV8_10SubstituteRat, manuscriptNormV8_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_10Interval.1 manuscriptNormV8_10Interval.2 manuscriptNormV8_10SubstituteRat
    (-2207517269453298436964373209 / 250000000000000000000000000000) (-4415034538906596873448011269 / 500000000000000000000000000000) manuscriptNormV8_10Term
    manuscriptNormV8_10_exact_interval hq manuscriptNormV8_10_rounded_endpoints.1 manuscriptNormV8_10_rounded_endpoints.2
  have hw : ((-4415034538906596873448011269 / 500000000000000000000000000000) - (-2207517269453298436964373209 / 250000000000000000000000000000) : ℚ) = (480735149 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_11SubstituteRat_composition_error :
    |manuscriptNormV8_11Term - (manuscriptNormV8_11SubstituteRat : ℝ)| ≤ (((3492861061 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_11SubstituteRat ∈ Set.Icc manuscriptNormV8_11Interval.1 manuscriptNormV8_11Interval.2 := by
    simpa only [manuscriptNormV8_11SubstituteRat, manuscriptNormV8_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_11Interval.1 manuscriptNormV8_11Interval.2 manuscriptNormV8_11SubstituteRat
    (8010452334665209331488056821 / 250000000000000000000000000000) (16020904669330418666468974703 / 500000000000000000000000000000) manuscriptNormV8_11Term
    manuscriptNormV8_11_exact_interval hq manuscriptNormV8_11_rounded_endpoints.1 manuscriptNormV8_11_rounded_endpoints.2
  have hw : ((16020904669330418666468974703 / 500000000000000000000000000000) - (8010452334665209331488056821 / 250000000000000000000000000000) : ℚ) = (3492861061 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV8_12SubstituteRat_composition_error :
    |manuscriptNormV8_12Term - (manuscriptNormV8_12SubstituteRat : ℝ)| ≤ (((1217277327 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV8_12SubstituteRat ∈ Set.Icc manuscriptNormV8_12Interval.1 manuscriptNormV8_12Interval.2 := by
    simpa only [manuscriptNormV8_12SubstituteRat, manuscriptNormV8_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV8_12Interval.1 manuscriptNormV8_12Interval.2 manuscriptNormV8_12SubstituteRat
    (71351466364959732874330401 / 6250000000000000000000000000) (11416234618393557261110141487 / 1000000000000000000000000000000) manuscriptNormV8_12Term
    manuscriptNormV8_12_exact_interval hq manuscriptNormV8_12_rounded_endpoints.1 manuscriptNormV8_12_rounded_endpoints.2
  have hw : ((11416234618393557261110141487 / 1000000000000000000000000000000) - (71351466364959732874330401 / 6250000000000000000000000000) : ℚ) = (1217277327 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow8_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 8 (0, 0)) - (manuscriptNormVSubstituteRow8 : ℝ)| ≤ (((2152518772229 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV8_0SubstituteRat_composition_error
  have h1 := manuscriptNormV8_1SubstituteRat_composition_error
  have h2 := manuscriptNormV8_2SubstituteRat_composition_error
  have h3 := manuscriptNormV8_3SubstituteRat_composition_error
  have h4 := manuscriptNormV8_4SubstituteRat_composition_error
  have h5 := manuscriptNormV8_5SubstituteRat_composition_error
  have h6 := manuscriptNormV8_6SubstituteRat_composition_error
  have h7 := manuscriptNormV8_7SubstituteRat_composition_error
  have h8 := manuscriptNormV8_8SubstituteRat_composition_error
  have h9 := manuscriptNormV8_9SubstituteRat_composition_error
  have h10 := manuscriptNormV8_10SubstituteRat_composition_error
  have h11 := manuscriptNormV8_11SubstituteRat_composition_error
  have h12 := manuscriptNormV8_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV8_0Term + (manuscriptNormV8_1Term + (manuscriptNormV8_2Term + (manuscriptNormV8_3Term + (manuscriptNormV8_4Term + (manuscriptNormV8_5Term + (manuscriptNormV8_6Term + (manuscriptNormV8_7Term + (manuscriptNormV8_8Term + (manuscriptNormV8_9Term + (manuscriptNormV8_10Term + (manuscriptNormV8_11Term + (manuscriptNormV8_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow8 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow8
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

def manuscriptNormV8_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43)

private theorem manuscriptNormV8_0RoundedSubstituteRat_error :
    |(manuscriptNormV8_0SubstituteRat : ℝ) - (manuscriptNormV8_0RoundedSubstituteRat : ℝ)| ≤
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (119089937171181 / 5000000000000000) (229422864123923 / 10000000000000000) (0) (-1) (949 / 625) (7 / 43) (by norm_num) (by norm_num)
  have hw : |(((119089937171181 / 5000000000000000) : ℚ) : ℝ)| + |(((229422864123923 / 10000000000000000) : ℚ) : ℝ)| =
      (((93520547693257 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV8_1RoundedSubstituteRat_error :
    |(manuscriptNormV8_1SubstituteRat : ℝ) - (manuscriptNormV8_1RoundedSubstituteRat : ℝ)| ≤
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233) (by norm_num) (by norm_num)
  have hw : |(((17439989085201 / 2500000000000000) : ℚ) : ℝ)| + |(((33597567865583 / 5000000000000000) : ℚ) : ℝ)| =
      (((13695509207197 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV8_2RoundedSubstituteRat_error :
    |(manuscriptNormV8_2SubstituteRat : ℝ) - (manuscriptNormV8_2RoundedSubstituteRat : ℝ)| ≤
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num) (by norm_num)
  have hw : |(((9971941566429 / 2500000000000000) : ℚ) : ℝ)| + |(((19210618876707 / 5000000000000000) : ℚ) : ℝ)| =
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV8_3RoundedSubstituteRat_error :
    |(manuscriptNormV8_3SubstituteRat : ℝ) - (manuscriptNormV8_3RoundedSubstituteRat : ℝ)| ≤
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num) (by norm_num)
  have hw : |(((-19324262066907 / 2500000000000000) : ℚ) : ℝ)| + |(((-37227558060581 / 5000000000000000) : ℚ) : ℝ)| =
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV8_4RoundedSubstituteRat_error :
    |(manuscriptNormV8_4SubstituteRat : ℝ) - (manuscriptNormV8_4RoundedSubstituteRat : ℝ)| ≤
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num) (by norm_num)
  have hw : |(((91031408615547 / 5000000000000000) : ℚ) : ℝ)| + |(((175369027693701 / 10000000000000000) : ℚ) : ℝ)| =
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV8_5RoundedSubstituteRat_error :
    |(manuscriptNormV8_5SubstituteRat : ℝ) - (manuscriptNormV8_5RoundedSubstituteRat : ℝ)| ≤
      (((583577347045887 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-7675142212993 / 1000000000000000) : ℚ) : ℝ)| + |(((506825924915957 / 10000000000000000) : ℚ) : ℝ)| =
      (((583577347045887 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV8_6RoundedSubstituteRat_error :
    |(manuscriptNormV8_6SubstituteRat : ℝ) - (manuscriptNormV8_6RoundedSubstituteRat : ℝ)| ≤
      (((599270904878273 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((251798416946459 / 5000000000000000) : ℚ) : ℝ)| + |(((-19134814197071 / 2000000000000000) : ℚ) : ℝ)| =
      (((599270904878273 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1)

private theorem manuscriptNormV8_7RoundedSubstituteRat_error :
    |(manuscriptNormV8_7SubstituteRat : ℝ) - (manuscriptNormV8_7RoundedSubstituteRat : ℝ)| ≤
      (((473406586612213 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-473406586612213 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((473406586612213 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1)

private theorem manuscriptNormV8_8RoundedSubstituteRat_error :
    |(manuscriptNormV8_8SubstituteRat : ℝ) - (manuscriptNormV8_8RoundedSubstituteRat : ℝ)| ≤
      (((490799825477327 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-3545037307063 / 2000000000000000) : ℚ) : ℝ)| + |(((-118268659735503 / 2500000000000000) : ℚ) : ℝ)| =
      (((490799825477327 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV8_9RoundedSubstituteRat_error :
    |(manuscriptNormV8_9SubstituteRat : ℝ) - (manuscriptNormV8_9RoundedSubstituteRat : ℝ)| ≤
      (((90655810620933 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((37458406176029 / 10000000000000000) : ℚ) : ℝ)| + |(((-143853215065837 / 10000000000000000) : ℚ) : ℝ)| =
      (((90655810620933 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV8_10RoundedSubstituteRat_error :
    |(manuscriptNormV8_10SubstituteRat : ℝ) - (manuscriptNormV8_10RoundedSubstituteRat : ℝ)| ≤
      (((23146012346453 / 1250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-142349837215793 / 10000000000000000) : ℚ) : ℝ)| + |(((42818261555831 / 10000000000000000) : ℚ) : ℝ)| =
      (((23146012346453 / 1250000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1)

private theorem manuscriptNormV8_11RoundedSubstituteRat_error :
    |(manuscriptNormV8_11SubstituteRat : ℝ) - (manuscriptNormV8_11RoundedSubstituteRat : ℝ)| ≤
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-295581257499211 / 20000000000000000) (371321316540867 / 20000000000000000) (-7) (0) (654368 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-295581257499211 / 20000000000000000) : ℚ) : ℝ)| + |(((371321316540867 / 20000000000000000) : ℚ) : ℝ)| =
      (((333451287020039 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV8_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1)

private theorem manuscriptNormV8_12RoundedSubstituteRat_error :
    |(manuscriptNormV8_12SubstituteRat : ℝ) - (manuscriptNormV8_12RoundedSubstituteRat : ℝ)| ≤
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (359993860770103 / 20000000000000000) (-309276931099449 / 20000000000000000) (1) (0) (5555449 / 3125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((359993860770103 / 20000000000000000) : ℚ) : ℝ)| + |(((-309276931099449 / 20000000000000000) : ℚ) : ℝ)| =
      (((41829424491847 / 1250000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow8 : ℚ :=
  manuscriptNormV8_0RoundedSubstituteRat +
    manuscriptNormV8_1RoundedSubstituteRat +
    manuscriptNormV8_2RoundedSubstituteRat +
    manuscriptNormV8_3RoundedSubstituteRat +
    manuscriptNormV8_4RoundedSubstituteRat +
    manuscriptNormV8_5RoundedSubstituteRat +
    manuscriptNormV8_6RoundedSubstituteRat +
    manuscriptNormV8_7RoundedSubstituteRat +
    manuscriptNormV8_8RoundedSubstituteRat +
    manuscriptNormV8_9RoundedSubstituteRat +
    manuscriptNormV8_10RoundedSubstituteRat +
    manuscriptNormV8_11RoundedSubstituteRat +
    manuscriptNormV8_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow8_error :
    |(manuscriptNormVSubstituteRow8 : ℝ) - (manuscriptNormVRoundedSubstituteRow8 : ℝ)| ≤
      (((174946876434119 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV8_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV8_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV8_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV8_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV8_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV8_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV8_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV8_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV8_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV8_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV8_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV8_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV8_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow8 manuscriptNormVRoundedSubstituteRow8
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

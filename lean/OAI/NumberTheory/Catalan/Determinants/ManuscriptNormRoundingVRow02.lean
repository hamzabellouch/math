import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup008
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup009
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup010
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup011
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup012
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV2_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV2_0SubstituteRat_interval :
    manuscriptNormV2_0SubstituteRat ∈ Set.Icc manuscriptNormV2_0Interval.1 manuscriptNormV2_0Interval.2 := by
  simpa only [manuscriptNormV2_0SubstituteRat, manuscriptNormV2_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormV2_0SubstituteRat_upper :
    manuscriptNormV2_0SubstituteRat ≤ (-103099457200427952149476101 / 50000000000000000000000000000) :=
  manuscriptNormV2_0SubstituteRat_interval.2.trans manuscriptNormV2_0_rounded_endpoints.2

def manuscriptNormV2_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV2_1SubstituteRat_interval :
    manuscriptNormV2_1SubstituteRat ∈ Set.Icc manuscriptNormV2_1Interval.1 manuscriptNormV2_1Interval.2 := by
  simpa only [manuscriptNormV2_1SubstituteRat, manuscriptNormV2_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num))

private theorem manuscriptNormV2_1SubstituteRat_upper :
    manuscriptNormV2_1SubstituteRat ≤ (-693892837680188433904874467 / 1000000000000000000000000000000) :=
  manuscriptNormV2_1SubstituteRat_interval.2.trans manuscriptNormV2_1_rounded_endpoints.2

def manuscriptNormV2_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1)

private theorem manuscriptNormV2_2SubstituteRat_interval :
    manuscriptNormV2_2SubstituteRat ∈ Set.Icc manuscriptNormV2_2Interval.1 manuscriptNormV2_2Interval.2 := by
  simpa only [manuscriptNormV2_2SubstituteRat, manuscriptNormV2_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV2_2SubstituteRat_upper :
    manuscriptNormV2_2SubstituteRat ≤ (964725351530545426839822669 / 1000000000000000000000000000000) :=
  manuscriptNormV2_2SubstituteRat_interval.2.trans manuscriptNormV2_2_rounded_endpoints.2

def manuscriptNormV2_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV2_3SubstituteRat_interval :
    manuscriptNormV2_3SubstituteRat ∈ Set.Icc manuscriptNormV2_3Interval.1 manuscriptNormV2_3Interval.2 := by
  simpa only [manuscriptNormV2_3SubstituteRat, manuscriptNormV2_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV2_3SubstituteRat_upper :
    manuscriptNormV2_3SubstituteRat ≤ (-2269897869559953121278620449 / 1000000000000000000000000000000) :=
  manuscriptNormV2_3SubstituteRat_interval.2.trans manuscriptNormV2_3_rounded_endpoints.2

def manuscriptNormV2_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV2_4SubstituteRat_interval :
    manuscriptNormV2_4SubstituteRat ∈ Set.Icc manuscriptNormV2_4Interval.1 manuscriptNormV2_4Interval.2 := by
  simpa only [manuscriptNormV2_4SubstituteRat, manuscriptNormV2_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV2_4SubstituteRat_upper :
    manuscriptNormV2_4SubstituteRat ≤ (2971062291974073186134220553 / 500000000000000000000000000000) :=
  manuscriptNormV2_4SubstituteRat_interval.2.trans manuscriptNormV2_4_rounded_endpoints.2

def manuscriptNormV2_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV2_5SubstituteRat_interval :
    manuscriptNormV2_5SubstituteRat ∈ Set.Icc manuscriptNormV2_5Interval.1 manuscriptNormV2_5Interval.2 := by
  simpa only [manuscriptNormV2_5SubstituteRat, manuscriptNormV2_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num))

private theorem manuscriptNormV2_5SubstituteRat_upper :
    manuscriptNormV2_5SubstituteRat ≤ (-903158177774137849737278943 / 250000000000000000000000000000) :=
  manuscriptNormV2_5SubstituteRat_interval.2.trans manuscriptNormV2_5_rounded_endpoints.2

def manuscriptNormV2_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527)

private theorem manuscriptNormV2_6SubstituteRat_interval :
    manuscriptNormV2_6SubstituteRat ∈ Set.Icc manuscriptNormV2_6Interval.1 manuscriptNormV2_6Interval.2 := by
  simpa only [manuscriptNormV2_6SubstituteRat, manuscriptNormV2_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527) (by norm_num))

private theorem manuscriptNormV2_6SubstituteRat_upper :
    manuscriptNormV2_6SubstituteRat ≤ (-903158177774137849737278943 / 250000000000000000000000000000) :=
  manuscriptNormV2_6SubstituteRat_interval.2.trans manuscriptNormV2_6_rounded_endpoints.2

def manuscriptNormV2_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112)

private theorem manuscriptNormV2_7SubstituteRat_interval :
    manuscriptNormV2_7SubstituteRat ∈ Set.Icc manuscriptNormV2_7Interval.1 manuscriptNormV2_7Interval.2 := by
  simpa only [manuscriptNormV2_7SubstituteRat, manuscriptNormV2_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112) (by norm_num))

private theorem manuscriptNormV2_7SubstituteRat_upper :
    manuscriptNormV2_7SubstituteRat ≤ (-400638762523047475177650967 / 250000000000000000000000000000) :=
  manuscriptNormV2_7SubstituteRat_interval.2.trans manuscriptNormV2_7_rounded_endpoints.2

def manuscriptNormV2_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV2_8SubstituteRat_interval :
    manuscriptNormV2_8SubstituteRat ∈ Set.Icc manuscriptNormV2_8Interval.1 manuscriptNormV2_8Interval.2 := by
  simpa only [manuscriptNormV2_8SubstituteRat, manuscriptNormV2_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num))

private theorem manuscriptNormV2_8SubstituteRat_upper :
    manuscriptNormV2_8SubstituteRat ≤ (-400638762523047475177650967 / 250000000000000000000000000000) :=
  manuscriptNormV2_8SubstituteRat_interval.2.trans manuscriptNormV2_8_rounded_endpoints.2

def manuscriptNormV2_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601)

private theorem manuscriptNormV2_9SubstituteRat_interval :
    manuscriptNormV2_9SubstituteRat ∈ Set.Icc manuscriptNormV2_9Interval.1 manuscriptNormV2_9Interval.2 := by
  simpa only [manuscriptNormV2_9SubstituteRat, manuscriptNormV2_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601) (by norm_num))

private theorem manuscriptNormV2_9SubstituteRat_upper :
    manuscriptNormV2_9SubstituteRat ≤ (643579885822160983031310613 / 500000000000000000000000000000) :=
  manuscriptNormV2_9SubstituteRat_interval.2.trans manuscriptNormV2_9_rounded_endpoints.2

def manuscriptNormV2_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV2_10SubstituteRat_interval :
    manuscriptNormV2_10SubstituteRat ∈ Set.Icc manuscriptNormV2_10Interval.1 manuscriptNormV2_10Interval.2 := by
  simpa only [manuscriptNormV2_10SubstituteRat, manuscriptNormV2_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num))

private theorem manuscriptNormV2_10SubstituteRat_upper :
    manuscriptNormV2_10SubstituteRat ≤ (643579885822160983031310613 / 500000000000000000000000000000) :=
  manuscriptNormV2_10SubstituteRat_interval.2.trans manuscriptNormV2_10_rounded_endpoints.2

def manuscriptNormV2_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV2_11SubstituteRat_interval :
    manuscriptNormV2_11SubstituteRat ∈ Set.Icc manuscriptNormV2_11Interval.1 manuscriptNormV2_11Interval.2 := by
  simpa only [manuscriptNormV2_11SubstituteRat, manuscriptNormV2_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num))

private theorem manuscriptNormV2_11SubstituteRat_upper :
    manuscriptNormV2_11SubstituteRat ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) :=
  manuscriptNormV2_11SubstituteRat_interval.2.trans manuscriptNormV2_11_rounded_endpoints.2

def manuscriptNormV2_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV2_12SubstituteRat_interval :
    manuscriptNormV2_12SubstituteRat ∈ Set.Icc manuscriptNormV2_12Interval.1 manuscriptNormV2_12Interval.2 := by
  simpa only [manuscriptNormV2_12SubstituteRat, manuscriptNormV2_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num))

private theorem manuscriptNormV2_12SubstituteRat_upper :
    manuscriptNormV2_12SubstituteRat ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) :=
  manuscriptNormV2_12SubstituteRat_interval.2.trans manuscriptNormV2_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow2 : ℚ :=
  manuscriptNormV2_0SubstituteRat +
    manuscriptNormV2_1SubstituteRat +
    manuscriptNormV2_2SubstituteRat +
    manuscriptNormV2_3SubstituteRat +
    manuscriptNormV2_4SubstituteRat +
    manuscriptNormV2_5SubstituteRat +
    manuscriptNormV2_6SubstituteRat +
    manuscriptNormV2_7SubstituteRat +
    manuscriptNormV2_8SubstituteRat +
    manuscriptNormV2_9SubstituteRat +
    manuscriptNormV2_10SubstituteRat +
    manuscriptNormV2_11SubstituteRat +
    manuscriptNormV2_12SubstituteRat

theorem manuscriptNormVSubstituteRow2_upper : manuscriptNormVSubstituteRow2 ≤ (-10066148211075587538820009047 / 1000000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow2
  linarith only [manuscriptNormV2_0SubstituteRat_upper,
    manuscriptNormV2_1SubstituteRat_upper,
    manuscriptNormV2_2SubstituteRat_upper,
    manuscriptNormV2_3SubstituteRat_upper,
    manuscriptNormV2_4SubstituteRat_upper,
    manuscriptNormV2_5SubstituteRat_upper,
    manuscriptNormV2_6SubstituteRat_upper,
    manuscriptNormV2_7SubstituteRat_upper,
    manuscriptNormV2_8SubstituteRat_upper,
    manuscriptNormV2_9SubstituteRat_upper,
    manuscriptNormV2_10SubstituteRat_upper,
    manuscriptNormV2_11SubstituteRat_upper,
    manuscriptNormV2_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV2_0SubstituteRat_composition_error :
    |manuscriptNormV2_0Term - (manuscriptNormV2_0SubstituteRat : ℝ)| ≤ (((65310217 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_0SubstituteRat ∈ Set.Icc manuscriptNormV2_0Interval.1 manuscriptNormV2_0Interval.2 := by
    simpa only [manuscriptNormV2_0SubstituteRat, manuscriptNormV2_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_0Interval.1 manuscriptNormV2_0Interval.2 manuscriptNormV2_0SubstituteRat
    (-257748643001069880406345361 / 125000000000000000000000000000) (-103099457200427952149476101 / 50000000000000000000000000000) manuscriptNormV2_0Term
    manuscriptNormV2_0_exact_interval hq manuscriptNormV2_0_rounded_endpoints.1 manuscriptNormV2_0_rounded_endpoints.2
  have hw : ((-103099457200427952149476101 / 50000000000000000000000000000) - (-257748643001069880406345361 / 125000000000000000000000000000) : ℚ) = (65310217 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_1SubstituteRat_composition_error :
    |manuscriptNormV2_1Term - (manuscriptNormV2_1SubstituteRat : ℝ)| ≤ (((76521359 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_1SubstituteRat ∈ Set.Icc manuscriptNormV2_1Interval.1 manuscriptNormV2_1Interval.2 := by
    simpa only [manuscriptNormV2_1SubstituteRat, manuscriptNormV2_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_1Interval.1 manuscriptNormV2_1Interval.2 manuscriptNormV2_1SubstituteRat
    (-346946418840094216990697913 / 500000000000000000000000000000) (-693892837680188433904874467 / 1000000000000000000000000000000) manuscriptNormV2_1Term
    manuscriptNormV2_1_exact_interval hq manuscriptNormV2_1_rounded_endpoints.1 manuscriptNormV2_1_rounded_endpoints.2
  have hw : ((-693892837680188433904874467 / 1000000000000000000000000000000) - (-346946418840094216990697913 / 500000000000000000000000000000) : ℚ) = (76521359 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_2SubstituteRat_composition_error :
    |manuscriptNormV2_2Term - (manuscriptNormV2_2SubstituteRat : ℝ)| ≤ (((2734363 / 12500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_2SubstituteRat ∈ Set.Icc manuscriptNormV2_2Interval.1 manuscriptNormV2_2Interval.2 := by
    simpa only [manuscriptNormV2_2SubstituteRat, manuscriptNormV2_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_2Interval.1 manuscriptNormV2_2Interval.2 manuscriptNormV2_2SubstituteRat
    (964725351530545426621073629 / 1000000000000000000000000000000) (964725351530545426839822669 / 1000000000000000000000000000000) manuscriptNormV2_2Term
    manuscriptNormV2_2_exact_interval hq manuscriptNormV2_2_rounded_endpoints.1 manuscriptNormV2_2_rounded_endpoints.2
  have hw : ((964725351530545426839822669 / 1000000000000000000000000000000) - (964725351530545426621073629 / 1000000000000000000000000000000) : ℚ) = (2734363 / 12500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_3SubstituteRat_composition_error :
    |manuscriptNormV2_3Term - (manuscriptNormV2_3SubstituteRat : ℝ)| ≤ (((63587919 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_3SubstituteRat ∈ Set.Icc manuscriptNormV2_3Interval.1 manuscriptNormV2_3Interval.2 := by
    simpa only [manuscriptNormV2_3SubstituteRat, manuscriptNormV2_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_3Interval.1 manuscriptNormV2_3Interval.2 manuscriptNormV2_3SubstituteRat
    (-2269897869559953121787323801 / 1000000000000000000000000000000) (-2269897869559953121278620449 / 1000000000000000000000000000000) manuscriptNormV2_3Term
    manuscriptNormV2_3_exact_interval hq manuscriptNormV2_3_rounded_endpoints.1 manuscriptNormV2_3_rounded_endpoints.2
  have hw : ((-2269897869559953121278620449 / 1000000000000000000000000000000) - (-2269897869559953121787323801 / 1000000000000000000000000000000) : ℚ) = (63587919 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_4SubstituteRat_composition_error :
    |manuscriptNormV2_4Term - (manuscriptNormV2_4SubstituteRat : ℝ)| ≤ (((1198142749 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_4SubstituteRat ∈ Set.Icc manuscriptNormV2_4Interval.1 manuscriptNormV2_4Interval.2 := by
    simpa only [manuscriptNormV2_4SubstituteRat, manuscriptNormV2_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_4Interval.1 manuscriptNormV2_4Interval.2 manuscriptNormV2_4SubstituteRat
    (5942124583948146371070298357 / 1000000000000000000000000000000) (2971062291974073186134220553 / 500000000000000000000000000000) manuscriptNormV2_4Term
    manuscriptNormV2_4_exact_interval hq manuscriptNormV2_4_rounded_endpoints.1 manuscriptNormV2_4_rounded_endpoints.2
  have hw : ((2971062291974073186134220553 / 500000000000000000000000000000) - (5942124583948146371070298357 / 1000000000000000000000000000000) : ℚ) = (1198142749 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_5SubstituteRat_composition_error :
    |manuscriptNormV2_5Term - (manuscriptNormV2_5SubstituteRat : ℝ)| ≤ (((177391524833 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_5SubstituteRat ∈ Set.Icc manuscriptNormV2_5Interval.1 manuscriptNormV2_5Interval.2 := by
    simpa only [manuscriptNormV2_5SubstituteRat, manuscriptNormV2_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_5Interval.1 manuscriptNormV2_5Interval.2 manuscriptNormV2_5SubstituteRat
    (-722526542219310315268128121 / 200000000000000000000000000000) (-903158177774137849737278943 / 250000000000000000000000000000) manuscriptNormV2_5Term
    manuscriptNormV2_5_exact_interval hq manuscriptNormV2_5_rounded_endpoints.1 manuscriptNormV2_5_rounded_endpoints.2
  have hw : ((-903158177774137849737278943 / 250000000000000000000000000000) - (-722526542219310315268128121 / 200000000000000000000000000000) : ℚ) = (177391524833 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_6SubstituteRat_composition_error :
    |manuscriptNormV2_6Term - (manuscriptNormV2_6SubstituteRat : ℝ)| ≤ (((177391524833 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_6SubstituteRat ∈ Set.Icc manuscriptNormV2_6Interval.1 manuscriptNormV2_6Interval.2 := by
    simpa only [manuscriptNormV2_6SubstituteRat, manuscriptNormV2_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_6Interval.1 manuscriptNormV2_6Interval.2 manuscriptNormV2_6SubstituteRat
    (-722526542219310315268128121 / 200000000000000000000000000000) (-903158177774137849737278943 / 250000000000000000000000000000) manuscriptNormV2_6Term
    manuscriptNormV2_6_exact_interval hq manuscriptNormV2_6_rounded_endpoints.1 manuscriptNormV2_6_rounded_endpoints.2
  have hw : ((-903158177774137849737278943 / 250000000000000000000000000000) - (-722526542219310315268128121 / 200000000000000000000000000000) : ℚ) = (177391524833 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_7SubstituteRat_composition_error :
    |manuscriptNormV2_7Term - (manuscriptNormV2_7SubstituteRat : ℝ)| ≤ (((69642682819 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_7SubstituteRat ∈ Set.Icc manuscriptNormV2_7Interval.1 manuscriptNormV2_7Interval.2 := by
    simpa only [manuscriptNormV2_7SubstituteRat, manuscriptNormV2_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_7Interval.1 manuscriptNormV2_7Interval.2 manuscriptNormV2_7SubstituteRat
    (-801277525046095019997984753 / 500000000000000000000000000000) (-400638762523047475177650967 / 250000000000000000000000000000) manuscriptNormV2_7Term
    manuscriptNormV2_7_exact_interval hq manuscriptNormV2_7_rounded_endpoints.1 manuscriptNormV2_7_rounded_endpoints.2
  have hw : ((-400638762523047475177650967 / 250000000000000000000000000000) - (-801277525046095019997984753 / 500000000000000000000000000000) : ℚ) = (69642682819 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_8SubstituteRat_composition_error :
    |manuscriptNormV2_8Term - (manuscriptNormV2_8SubstituteRat : ℝ)| ≤ (((69642682819 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_8SubstituteRat ∈ Set.Icc manuscriptNormV2_8Interval.1 manuscriptNormV2_8Interval.2 := by
    simpa only [manuscriptNormV2_8SubstituteRat, manuscriptNormV2_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_8Interval.1 manuscriptNormV2_8Interval.2 manuscriptNormV2_8SubstituteRat
    (-801277525046095019997984753 / 500000000000000000000000000000) (-400638762523047475177650967 / 250000000000000000000000000000) manuscriptNormV2_8Term
    manuscriptNormV2_8_exact_interval hq manuscriptNormV2_8_rounded_endpoints.1 manuscriptNormV2_8_rounded_endpoints.2
  have hw : ((-400638762523047475177650967 / 250000000000000000000000000000) - (-801277525046095019997984753 / 500000000000000000000000000000) : ℚ) = (69642682819 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_9SubstituteRat_composition_error :
    |manuscriptNormV2_9Term - (manuscriptNormV2_9SubstituteRat : ℝ)| ≤ (((3435056221 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_9SubstituteRat ∈ Set.Icc manuscriptNormV2_9Interval.1 manuscriptNormV2_9Interval.2 := by
    simpa only [manuscriptNormV2_9SubstituteRat, manuscriptNormV2_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_9Interval.1 manuscriptNormV2_9Interval.2 manuscriptNormV2_9SubstituteRat
    (128715977164432191110172169 / 100000000000000000000000000000) (643579885822160983031310613 / 500000000000000000000000000000) manuscriptNormV2_9Term
    manuscriptNormV2_9_exact_interval hq manuscriptNormV2_9_rounded_endpoints.1 manuscriptNormV2_9_rounded_endpoints.2
  have hw : ((643579885822160983031310613 / 500000000000000000000000000000) - (128715977164432191110172169 / 100000000000000000000000000000) : ℚ) = (3435056221 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_10SubstituteRat_composition_error :
    |manuscriptNormV2_10Term - (manuscriptNormV2_10SubstituteRat : ℝ)| ≤ (((3435056221 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_10SubstituteRat ∈ Set.Icc manuscriptNormV2_10Interval.1 manuscriptNormV2_10Interval.2 := by
    simpa only [manuscriptNormV2_10SubstituteRat, manuscriptNormV2_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_10Interval.1 manuscriptNormV2_10Interval.2 manuscriptNormV2_10SubstituteRat
    (128715977164432191110172169 / 100000000000000000000000000000) (643579885822160983031310613 / 500000000000000000000000000000) manuscriptNormV2_10Term
    manuscriptNormV2_10_exact_interval hq manuscriptNormV2_10_rounded_endpoints.1 manuscriptNormV2_10_rounded_endpoints.2
  have hw : ((643579885822160983031310613 / 500000000000000000000000000000) - (128715977164432191110172169 / 100000000000000000000000000000) : ℚ) = (3435056221 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_11SubstituteRat_composition_error :
    |manuscriptNormV2_11Term - (manuscriptNormV2_11SubstituteRat : ℝ)| ≤ (((6262052587 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_11SubstituteRat ∈ Set.Icc manuscriptNormV2_11Interval.1 manuscriptNormV2_11Interval.2 := by
    simpa only [manuscriptNormV2_11SubstituteRat, manuscriptNormV2_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_11Interval.1 manuscriptNormV2_11Interval.2 manuscriptNormV2_11SubstituteRat
    (-2045581158108370136473370921 / 1000000000000000000000000000000) (-2045581158108370036280529529 / 1000000000000000000000000000000) manuscriptNormV2_11Term
    manuscriptNormV2_11_exact_interval hq manuscriptNormV2_11_rounded_endpoints.1 manuscriptNormV2_11_rounded_endpoints.2
  have hw : ((-2045581158108370036280529529 / 1000000000000000000000000000000) - (-2045581158108370136473370921 / 1000000000000000000000000000000) : ℚ) = (6262052587 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV2_12SubstituteRat_composition_error :
    |manuscriptNormV2_12Term - (manuscriptNormV2_12SubstituteRat : ℝ)| ≤ (((6262052587 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV2_12SubstituteRat ∈ Set.Icc manuscriptNormV2_12Interval.1 manuscriptNormV2_12Interval.2 := by
    simpa only [manuscriptNormV2_12SubstituteRat, manuscriptNormV2_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV2_12Interval.1 manuscriptNormV2_12Interval.2 manuscriptNormV2_12SubstituteRat
    (-2045581158108370136473370921 / 1000000000000000000000000000000) (-2045581158108370036280529529 / 1000000000000000000000000000000) manuscriptNormV2_12Term
    manuscriptNormV2_12_exact_interval hq manuscriptNormV2_12_rounded_endpoints.1 manuscriptNormV2_12_rounded_endpoints.2
  have hw : ((-2045581158108370036280529529 / 1000000000000000000000000000000) - (-2045581158108370136473370921 / 1000000000000000000000000000000) : ℚ) = (6262052587 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow2_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 2 (0, 0)) - (manuscriptNormVSubstituteRow2 : ℝ)| ≤ (((472962310083 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV2_0SubstituteRat_composition_error
  have h1 := manuscriptNormV2_1SubstituteRat_composition_error
  have h2 := manuscriptNormV2_2SubstituteRat_composition_error
  have h3 := manuscriptNormV2_3SubstituteRat_composition_error
  have h4 := manuscriptNormV2_4SubstituteRat_composition_error
  have h5 := manuscriptNormV2_5SubstituteRat_composition_error
  have h6 := manuscriptNormV2_6SubstituteRat_composition_error
  have h7 := manuscriptNormV2_7SubstituteRat_composition_error
  have h8 := manuscriptNormV2_8SubstituteRat_composition_error
  have h9 := manuscriptNormV2_9SubstituteRat_composition_error
  have h10 := manuscriptNormV2_10SubstituteRat_composition_error
  have h11 := manuscriptNormV2_11SubstituteRat_composition_error
  have h12 := manuscriptNormV2_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV2_0Term + (manuscriptNormV2_1Term + (manuscriptNormV2_2Term + (manuscriptNormV2_3Term + (manuscriptNormV2_4Term + (manuscriptNormV2_5Term + (manuscriptNormV2_6Term + (manuscriptNormV2_7Term + (manuscriptNormV2_8Term + (manuscriptNormV2_9Term + (manuscriptNormV2_10Term + (manuscriptNormV2_11Term + (manuscriptNormV2_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow2 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow2
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

def manuscriptNormV2_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV2_0RoundedSubstituteRat_error :
    |(manuscriptNormV2_0SubstituteRat : ℝ) - (manuscriptNormV2_0RoundedSubstituteRat : ℝ)| ≤
      (((19344020640489 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-19344020640489 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((19344020640489 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV2_1RoundedSubstituteRat_error :
    |(manuscriptNormV2_1SubstituteRat : ℝ) - (manuscriptNormV2_1RoundedSubstituteRat : ℝ)| ≤
      (((2832812887869 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2832812887869 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((2832812887869 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1)

private theorem manuscriptNormV2_2RoundedSubstituteRat_error :
    |(manuscriptNormV2_2SubstituteRat : ℝ) - (manuscriptNormV2_2RoundedSubstituteRat : ℝ)| ≤
      (((1619762744601 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-1619762744601 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((1619762744601 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV2_3RoundedSubstituteRat_error :
    |(manuscriptNormV2_3SubstituteRat : ℝ) - (manuscriptNormV2_3RoundedSubstituteRat : ℝ)| ≤
      (((3138879179583 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((3138879179583 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((3138879179583 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV2_4RoundedSubstituteRat_error :
    |(manuscriptNormV2_4SubstituteRat : ℝ) - (manuscriptNormV2_4RoundedSubstituteRat : ℝ)| ≤
      (((14786416795743 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-14786416795743 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((14786416795743 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV2_5RoundedSubstituteRat_error :
    |(manuscriptNormV2_5SubstituteRat : ℝ) - (manuscriptNormV2_5RoundedSubstituteRat : ℝ)| ≤
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num) (by norm_num)
  have hw : |(((-17333342034543 / 5000000000000000) : ℚ) : ℝ)| + |(((-764572651551 / 156250000000000) : ℚ) : ℝ)| =
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527)

private theorem manuscriptNormV2_6RoundedSubstituteRat_error :
    |(manuscriptNormV2_6SubstituteRat : ℝ) - (manuscriptNormV2_6RoundedSubstituteRat : ℝ)| ≤
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527) (by norm_num) (by norm_num)
  have hw : |(((-17333342034543 / 5000000000000000) : ℚ) : ℝ)| + |(((764572651551 / 156250000000000) : ℚ) : ℝ)| =
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112)

private theorem manuscriptNormV2_7RoundedSubstituteRat_error :
    |(manuscriptNormV2_7SubstituteRat : ℝ) - (manuscriptNormV2_7RoundedSubstituteRat : ℝ)| ≤
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112) (by norm_num) (by norm_num)
  have hw : |(((9971941566429 / 2500000000000000) : ℚ) : ℝ)| + |(((-19210618876707 / 5000000000000000) : ℚ) : ℝ)| =
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112)

private theorem manuscriptNormV2_8RoundedSubstituteRat_error :
    |(manuscriptNormV2_8SubstituteRat : ℝ) - (manuscriptNormV2_8RoundedSubstituteRat : ℝ)| ≤
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (9971941566429 / 2500000000000000) (19210618876707 / 5000000000000000) (0) (1) (25426 / 15625) (-13 / 112) (by norm_num) (by norm_num)
  have hw : |(((9971941566429 / 2500000000000000) : ℚ) : ℝ)| + |(((19210618876707 / 5000000000000000) : ℚ) : ℝ)| =
      (((7830900401913 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601)

private theorem manuscriptNormV2_9RoundedSubstituteRat_error :
    |(manuscriptNormV2_9SubstituteRat : ℝ) - (manuscriptNormV2_9RoundedSubstituteRat : ℝ)| ≤
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601) (by norm_num) (by norm_num)
  have hw : |(((4259432104929 / 5000000000000000) : ℚ) : ℝ)| + |(((7580356876773 / 5000000000000000) : ℚ) : ℝ)| =
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV2_10RoundedSubstituteRat_error :
    |(manuscriptNormV2_10SubstituteRat : ℝ) - (manuscriptNormV2_10RoundedSubstituteRat : ℝ)| ≤
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num) (by norm_num)
  have hw : |(((4259432104929 / 5000000000000000) : ℚ) : ℝ)| + |(((-7580356876773 / 5000000000000000) : ℚ) : ℝ)| =
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV2_11RoundedSubstituteRat_error :
    |(manuscriptNormV2_11SubstituteRat : ℝ) - (manuscriptNormV2_11RoundedSubstituteRat : ℝ)| ≤
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831) (by norm_num) (by norm_num)
  have hw : |(((-2615667529887 / 10000000000000000) : ℚ) : ℝ)| + |(((-27637739306451 / 10000000000000000) : ℚ) : ℝ)| =
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV2_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV2_12RoundedSubstituteRat_error :
    |(manuscriptNormV2_12SubstituteRat : ℝ) - (manuscriptNormV2_12RoundedSubstituteRat : ℝ)| ≤
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831) (by norm_num) (by norm_num)
  have hw : |(((-2615667529887 / 10000000000000000) : ℚ) : ℝ)| + |(((27637739306451 / 10000000000000000) : ℚ) : ℝ)| =
      (((15126703418169 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow2 : ℚ :=
  manuscriptNormV2_0RoundedSubstituteRat +
    manuscriptNormV2_1RoundedSubstituteRat +
    manuscriptNormV2_2RoundedSubstituteRat +
    manuscriptNormV2_3RoundedSubstituteRat +
    manuscriptNormV2_4RoundedSubstituteRat +
    manuscriptNormV2_5RoundedSubstituteRat +
    manuscriptNormV2_6RoundedSubstituteRat +
    manuscriptNormV2_7RoundedSubstituteRat +
    manuscriptNormV2_8RoundedSubstituteRat +
    manuscriptNormV2_9RoundedSubstituteRat +
    manuscriptNormV2_10RoundedSubstituteRat +
    manuscriptNormV2_11RoundedSubstituteRat +
    manuscriptNormV2_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow2_error :
    |(manuscriptNormVSubstituteRow2 : ℝ) - (manuscriptNormVRoundedSubstituteRow2 : ℝ)| ≤
      (((6628866741189 / 125000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV2_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV2_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV2_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV2_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV2_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV2_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV2_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV2_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV2_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV2_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV2_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV2_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV2_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow2 manuscriptNormVRoundedSubstituteRow2
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

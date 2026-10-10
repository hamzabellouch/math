import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup013
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup014
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup015
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup016
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup017
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV3_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV3_0SubstituteRat_interval :
    manuscriptNormV3_0SubstituteRat ∈ Set.Icc manuscriptNormV3_0Interval.1 manuscriptNormV3_0Interval.2 := by
  simpa only [manuscriptNormV3_0SubstituteRat, manuscriptNormV3_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num))

private theorem manuscriptNormV3_0SubstituteRat_upper :
    manuscriptNormV3_0SubstituteRat ≤ (4238278883534061783907706481 / 1000000000000000000000000000000) :=
  manuscriptNormV3_0SubstituteRat_interval.2.trans manuscriptNormV3_0_rounded_endpoints.2

def manuscriptNormV3_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV3_1SubstituteRat_interval :
    manuscriptNormV3_1SubstituteRat ∈ Set.Icc manuscriptNormV3_1Interval.1 manuscriptNormV3_1Interval.2 := by
  simpa only [manuscriptNormV3_1SubstituteRat, manuscriptNormV3_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormV3_1SubstituteRat_upper :
    manuscriptNormV3_1SubstituteRat ≤ (1423234542328589038633585387 / 1000000000000000000000000000000) :=
  manuscriptNormV3_1SubstituteRat_interval.2.trans manuscriptNormV3_1_rounded_endpoints.2

def manuscriptNormV3_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV3_2SubstituteRat_interval :
    manuscriptNormV3_2SubstituteRat ∈ Set.Icc manuscriptNormV3_2Interval.1 manuscriptNormV3_2Interval.2 := by
  simpa only [manuscriptNormV3_2SubstituteRat, manuscriptNormV3_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV3_2SubstituteRat_upper :
    manuscriptNormV3_2SubstituteRat ≤ (-2269897869559953121278620449 / 1000000000000000000000000000000) :=
  manuscriptNormV3_2SubstituteRat_interval.2.trans manuscriptNormV3_2_rounded_endpoints.2

def manuscriptNormV3_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1)

private theorem manuscriptNormV3_3SubstituteRat_interval :
    manuscriptNormV3_3SubstituteRat ∈ Set.Icc manuscriptNormV3_3Interval.1 manuscriptNormV3_3Interval.2 := by
  simpa only [manuscriptNormV3_3SubstituteRat, manuscriptNormV3_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1) (by norm_num))

private theorem manuscriptNormV3_3SubstituteRat_upper :
    manuscriptNormV3_3SubstituteRat ≤ (5663992189381425178592500627 / 1000000000000000000000000000000) :=
  manuscriptNormV3_3SubstituteRat_interval.2.trans manuscriptNormV3_3_rounded_endpoints.2

def manuscriptNormV3_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV3_4SubstituteRat_interval :
    manuscriptNormV3_4SubstituteRat ∈ Set.Icc manuscriptNormV3_4Interval.1 manuscriptNormV3_4Interval.2 := by
  simpa only [manuscriptNormV3_4SubstituteRat, manuscriptNormV3_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV3_4SubstituteRat_upper :
    manuscriptNormV3_4SubstituteRat ≤ (-97792568524825520647620519 / 6250000000000000000000000000) :=
  manuscriptNormV3_4SubstituteRat_interval.2.trans manuscriptNormV3_4_rounded_endpoints.2

def manuscriptNormV3_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV3_5SubstituteRat_interval :
    manuscriptNormV3_5SubstituteRat ∈ Set.Icc manuscriptNormV3_5Interval.1 manuscriptNormV3_5Interval.2 := by
  simpa only [manuscriptNormV3_5SubstituteRat, manuscriptNormV3_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num))

private theorem manuscriptNormV3_5SubstituteRat_upper :
    manuscriptNormV3_5SubstituteRat ≤ (1879305435759342300679999343 / 250000000000000000000000000000) :=
  manuscriptNormV3_5SubstituteRat_interval.2.trans manuscriptNormV3_5_rounded_endpoints.2

def manuscriptNormV3_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741)

private theorem manuscriptNormV3_6SubstituteRat_interval :
    manuscriptNormV3_6SubstituteRat ∈ Set.Icc manuscriptNormV3_6Interval.1 manuscriptNormV3_6Interval.2 := by
  simpa only [manuscriptNormV3_6SubstituteRat, manuscriptNormV3_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741) (by norm_num))

private theorem manuscriptNormV3_6SubstituteRat_upper :
    manuscriptNormV3_6SubstituteRat ≤ (1879305435759342300679999343 / 250000000000000000000000000000) :=
  manuscriptNormV3_6SubstituteRat_interval.2.trans manuscriptNormV3_6_rounded_endpoints.2

def manuscriptNormV3_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371)

private theorem manuscriptNormV3_7SubstituteRat_interval :
    manuscriptNormV3_7SubstituteRat ∈ Set.Icc manuscriptNormV3_7Interval.1 manuscriptNormV3_7Interval.2 := by
  simpa only [manuscriptNormV3_7SubstituteRat, manuscriptNormV3_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371) (by norm_num))

private theorem manuscriptNormV3_7SubstituteRat_upper :
    manuscriptNormV3_7SubstituteRat ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) :=
  manuscriptNormV3_7SubstituteRat_interval.2.trans manuscriptNormV3_7_rounded_endpoints.2

def manuscriptNormV3_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV3_8SubstituteRat_interval :
    manuscriptNormV3_8SubstituteRat ∈ Set.Icc manuscriptNormV3_8Interval.1 manuscriptNormV3_8Interval.2 := by
  simpa only [manuscriptNormV3_8SubstituteRat, manuscriptNormV3_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num))

private theorem manuscriptNormV3_8SubstituteRat_upper :
    manuscriptNormV3_8SubstituteRat ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) :=
  manuscriptNormV3_8SubstituteRat_interval.2.trans manuscriptNormV3_8_rounded_endpoints.2

def manuscriptNormV3_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629)

private theorem manuscriptNormV3_9SubstituteRat_interval :
    manuscriptNormV3_9SubstituteRat ∈ Set.Icc manuscriptNormV3_9Interval.1 manuscriptNormV3_9Interval.2 := by
  simpa only [manuscriptNormV3_9SubstituteRat, manuscriptNormV3_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629) (by norm_num))

private theorem manuscriptNormV3_9SubstituteRat_upper :
    manuscriptNormV3_9SubstituteRat ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) :=
  manuscriptNormV3_9SubstituteRat_interval.2.trans manuscriptNormV3_9_rounded_endpoints.2

def manuscriptNormV3_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV3_10SubstituteRat_interval :
    manuscriptNormV3_10SubstituteRat ∈ Set.Icc manuscriptNormV3_10Interval.1 manuscriptNormV3_10Interval.2 := by
  simpa only [manuscriptNormV3_10SubstituteRat, manuscriptNormV3_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num))

private theorem manuscriptNormV3_10SubstituteRat_upper :
    manuscriptNormV3_10SubstituteRat ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) :=
  manuscriptNormV3_10SubstituteRat_interval.2.trans manuscriptNormV3_10_rounded_endpoints.2

def manuscriptNormV3_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV3_11SubstituteRat_interval :
    manuscriptNormV3_11SubstituteRat ∈ Set.Icc manuscriptNormV3_11Interval.1 manuscriptNormV3_11Interval.2 := by
  simpa only [manuscriptNormV3_11SubstituteRat, manuscriptNormV3_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num))

private theorem manuscriptNormV3_11SubstituteRat_upper :
    manuscriptNormV3_11SubstituteRat ≤ (418519297172338085081844233 / 100000000000000000000000000000) :=
  manuscriptNormV3_11SubstituteRat_interval.2.trans manuscriptNormV3_11_rounded_endpoints.2

def manuscriptNormV3_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV3_12SubstituteRat_interval :
    manuscriptNormV3_12SubstituteRat ∈ Set.Icc manuscriptNormV3_12Interval.1 manuscriptNormV3_12Interval.2 := by
  simpa only [manuscriptNormV3_12SubstituteRat, manuscriptNormV3_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num))

private theorem manuscriptNormV3_12SubstituteRat_upper :
    manuscriptNormV3_12SubstituteRat ≤ (418519297172338085081844233 / 100000000000000000000000000000) :=
  manuscriptNormV3_12SubstituteRat_interval.2.trans manuscriptNormV3_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow3 : ℚ :=
  manuscriptNormV3_0SubstituteRat +
    manuscriptNormV3_1SubstituteRat +
    manuscriptNormV3_2SubstituteRat +
    manuscriptNormV3_3SubstituteRat +
    manuscriptNormV3_4SubstituteRat +
    manuscriptNormV3_5SubstituteRat +
    manuscriptNormV3_6SubstituteRat +
    manuscriptNormV3_7SubstituteRat +
    manuscriptNormV3_8SubstituteRat +
    manuscriptNormV3_9SubstituteRat +
    manuscriptNormV3_10SubstituteRat +
    manuscriptNormV3_11SubstituteRat +
    manuscriptNormV3_12SubstituteRat

theorem manuscriptNormVSubstituteRow3_upper : manuscriptNormVSubstituteRow3 ≤ (8892604089276253133653642727 / 500000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow3
  linarith only [manuscriptNormV3_0SubstituteRat_upper,
    manuscriptNormV3_1SubstituteRat_upper,
    manuscriptNormV3_2SubstituteRat_upper,
    manuscriptNormV3_3SubstituteRat_upper,
    manuscriptNormV3_4SubstituteRat_upper,
    manuscriptNormV3_5SubstituteRat_upper,
    manuscriptNormV3_6SubstituteRat_upper,
    manuscriptNormV3_7SubstituteRat_upper,
    manuscriptNormV3_8SubstituteRat_upper,
    manuscriptNormV3_9SubstituteRat_upper,
    manuscriptNormV3_10SubstituteRat_upper,
    manuscriptNormV3_11SubstituteRat_upper,
    manuscriptNormV3_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV3_0SubstituteRat_composition_error :
    |manuscriptNormV3_0Term - (manuscriptNormV3_0SubstituteRat : ℝ)| ≤ (((506249199 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_0SubstituteRat ∈ Set.Icc manuscriptNormV3_0Interval.1 manuscriptNormV3_0Interval.2 := by
    simpa only [manuscriptNormV3_0SubstituteRat, manuscriptNormV3_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_0Interval.1 manuscriptNormV3_0Interval.2 manuscriptNormV3_0SubstituteRat
    (2119139441767030891700728641 / 500000000000000000000000000000) (4238278883534061783907706481 / 1000000000000000000000000000000) manuscriptNormV3_0Term
    manuscriptNormV3_0_exact_interval hq manuscriptNormV3_0_rounded_endpoints.1 manuscriptNormV3_0_rounded_endpoints.2
  have hw : ((4238278883534061783907706481 / 1000000000000000000000000000000) - (2119139441767030891700728641 / 500000000000000000000000000000) : ℚ) = (506249199 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_1SubstituteRat_composition_error :
    |manuscriptNormV3_1Term - (manuscriptNormV3_1SubstituteRat : ℝ)| ≤ (((18682129 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_1SubstituteRat ∈ Set.Icc manuscriptNormV3_1Interval.1 manuscriptNormV3_1Interval.2 := by
    simpa only [manuscriptNormV3_1SubstituteRat, manuscriptNormV3_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_1Interval.1 manuscriptNormV3_1Interval.2 manuscriptNormV3_1SubstituteRat
    (284646908465717807696825671 / 200000000000000000000000000000) (1423234542328589038633585387 / 1000000000000000000000000000000) manuscriptNormV3_1Term
    manuscriptNormV3_1_exact_interval hq manuscriptNormV3_1_rounded_endpoints.1 manuscriptNormV3_1_rounded_endpoints.2
  have hw : ((1423234542328589038633585387 / 1000000000000000000000000000000) - (284646908465717807696825671 / 200000000000000000000000000000) : ℚ) = (18682129 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_2SubstituteRat_composition_error :
    |manuscriptNormV3_2Term - (manuscriptNormV3_2SubstituteRat : ℝ)| ≤ (((63587919 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_2SubstituteRat ∈ Set.Icc manuscriptNormV3_2Interval.1 manuscriptNormV3_2Interval.2 := by
    simpa only [manuscriptNormV3_2SubstituteRat, manuscriptNormV3_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_2Interval.1 manuscriptNormV3_2Interval.2 manuscriptNormV3_2SubstituteRat
    (-2269897869559953121787323801 / 1000000000000000000000000000000) (-2269897869559953121278620449 / 1000000000000000000000000000000) manuscriptNormV3_2Term
    manuscriptNormV3_2_exact_interval hq manuscriptNormV3_2_rounded_endpoints.1 manuscriptNormV3_2_rounded_endpoints.2
  have hw : ((-2269897869559953121278620449 / 1000000000000000000000000000000) - (-2269897869559953121787323801 / 1000000000000000000000000000000) : ℚ) = (63587919 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_3SubstituteRat_composition_error :
    |manuscriptNormV3_3Term - (manuscriptNormV3_3SubstituteRat : ℝ)| ≤ (((230011841 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_3SubstituteRat ∈ Set.Icc manuscriptNormV3_3Interval.1 manuscriptNormV3_3Interval.2 := by
    simpa only [manuscriptNormV3_3SubstituteRat, manuscriptNormV3_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_3Interval.1 manuscriptNormV3_3Interval.2 manuscriptNormV3_3SubstituteRat
    (2831996094690712588721220711 / 500000000000000000000000000000) (5663992189381425178592500627 / 1000000000000000000000000000000) manuscriptNormV3_3Term
    manuscriptNormV3_3_exact_interval hq manuscriptNormV3_3_rounded_endpoints.1 manuscriptNormV3_3_rounded_endpoints.2
  have hw : ((5663992189381425178592500627 / 1000000000000000000000000000000) - (2831996094690712588721220711 / 500000000000000000000000000000) : ℚ) = (230011841 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_4SubstituteRat_composition_error :
    |manuscriptNormV3_4Term - (manuscriptNormV3_4SubstituteRat : ℝ)| ≤ (((3095782879 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_4SubstituteRat ∈ Set.Icc manuscriptNormV3_4Interval.1 manuscriptNormV3_4Interval.2 := by
    simpa only [manuscriptNormV3_4SubstituteRat, manuscriptNormV3_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_4Interval.1 manuscriptNormV3_4Interval.2 manuscriptNormV3_4SubstituteRat
    (-15646810963972083306715065919 / 1000000000000000000000000000000) (-97792568524825520647620519 / 6250000000000000000000000000) manuscriptNormV3_4Term
    manuscriptNormV3_4_exact_interval hq manuscriptNormV3_4_rounded_endpoints.1 manuscriptNormV3_4_rounded_endpoints.2
  have hw : ((-97792568524825520647620519 / 6250000000000000000000000000) - (-15646810963972083306715065919 / 1000000000000000000000000000000) : ℚ) = (3095782879 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_5SubstituteRat_composition_error :
    |manuscriptNormV3_5Term - (manuscriptNormV3_5SubstituteRat : ℝ)| ≤ (((343760569783 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_5SubstituteRat ∈ Set.Icc manuscriptNormV3_5Interval.1 manuscriptNormV3_5Interval.2 := by
    simpa only [manuscriptNormV3_5SubstituteRat, manuscriptNormV3_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_5Interval.1 manuscriptNormV3_5Interval.2 manuscriptNormV3_5SubstituteRat
    (7517221743037368858959427589 / 1000000000000000000000000000000) (1879305435759342300679999343 / 250000000000000000000000000000) manuscriptNormV3_5Term
    manuscriptNormV3_5_exact_interval hq manuscriptNormV3_5_rounded_endpoints.1 manuscriptNormV3_5_rounded_endpoints.2
  have hw : ((1879305435759342300679999343 / 250000000000000000000000000000) - (7517221743037368858959427589 / 1000000000000000000000000000000) : ℚ) = (343760569783 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_6SubstituteRat_composition_error :
    |manuscriptNormV3_6Term - (manuscriptNormV3_6SubstituteRat : ℝ)| ≤ (((343760569783 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_6SubstituteRat ∈ Set.Icc manuscriptNormV3_6Interval.1 manuscriptNormV3_6Interval.2 := by
    simpa only [manuscriptNormV3_6SubstituteRat, manuscriptNormV3_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_6Interval.1 manuscriptNormV3_6Interval.2 manuscriptNormV3_6SubstituteRat
    (7517221743037368858959427589 / 1000000000000000000000000000000) (1879305435759342300679999343 / 250000000000000000000000000000) manuscriptNormV3_6Term
    manuscriptNormV3_6_exact_interval hq manuscriptNormV3_6_rounded_endpoints.1 manuscriptNormV3_6_rounded_endpoints.2
  have hw : ((1879305435759342300679999343 / 250000000000000000000000000000) - (7517221743037368858959427589 / 1000000000000000000000000000000) : ℚ) = (343760569783 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_7SubstituteRat_composition_error :
    |manuscriptNormV3_7Term - (manuscriptNormV3_7SubstituteRat : ℝ)| ≤ (((33739522489 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_7SubstituteRat ∈ Set.Icc manuscriptNormV3_7Interval.1 manuscriptNormV3_7Interval.2 := by
    simpa only [manuscriptNormV3_7SubstituteRat, manuscriptNormV3_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_7Interval.1 manuscriptNormV3_7Interval.2 manuscriptNormV3_7SubstituteRat
    (3146180457411023770175562599 / 1000000000000000000000000000000) (3146180457411024040091742511 / 1000000000000000000000000000000) manuscriptNormV3_7Term
    manuscriptNormV3_7_exact_interval hq manuscriptNormV3_7_rounded_endpoints.1 manuscriptNormV3_7_rounded_endpoints.2
  have hw : ((3146180457411024040091742511 / 1000000000000000000000000000000) - (3146180457411023770175562599 / 1000000000000000000000000000000) : ℚ) = (33739522489 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_8SubstituteRat_composition_error :
    |manuscriptNormV3_8Term - (manuscriptNormV3_8SubstituteRat : ℝ)| ≤ (((33739522489 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_8SubstituteRat ∈ Set.Icc manuscriptNormV3_8Interval.1 manuscriptNormV3_8Interval.2 := by
    simpa only [manuscriptNormV3_8SubstituteRat, manuscriptNormV3_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_8Interval.1 manuscriptNormV3_8Interval.2 manuscriptNormV3_8SubstituteRat
    (3146180457411023770175562599 / 1000000000000000000000000000000) (3146180457411024040091742511 / 1000000000000000000000000000000) manuscriptNormV3_8Term
    manuscriptNormV3_8_exact_interval hq manuscriptNormV3_8_rounded_endpoints.1 manuscriptNormV3_8_rounded_endpoints.2
  have hw : ((3146180457411024040091742511 / 1000000000000000000000000000000) - (3146180457411023770175562599 / 1000000000000000000000000000000) : ℚ) = (33739522489 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_9SubstituteRat_composition_error :
    |manuscriptNormV3_9Term - (manuscriptNormV3_9SubstituteRat : ℝ)| ≤ (((106507475189 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_9SubstituteRat ∈ Set.Icc manuscriptNormV3_9Interval.1 manuscriptNormV3_9Interval.2 := by
    simpa only [manuscriptNormV3_9SubstituteRat, manuscriptNormV3_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_9Interval.1 manuscriptNormV3_9Interval.2 manuscriptNormV3_9SubstituteRat
    (-1330194736875770427300979589 / 500000000000000000000000000000) (-2660389473751540748094483989 / 1000000000000000000000000000000) manuscriptNormV3_9Term
    manuscriptNormV3_9_exact_interval hq manuscriptNormV3_9_rounded_endpoints.1 manuscriptNormV3_9_rounded_endpoints.2
  have hw : ((-2660389473751540748094483989 / 1000000000000000000000000000000) - (-1330194736875770427300979589 / 500000000000000000000000000000) : ℚ) = (106507475189 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_10SubstituteRat_composition_error :
    |manuscriptNormV3_10Term - (manuscriptNormV3_10SubstituteRat : ℝ)| ≤ (((106507475189 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_10SubstituteRat ∈ Set.Icc manuscriptNormV3_10Interval.1 manuscriptNormV3_10Interval.2 := by
    simpa only [manuscriptNormV3_10SubstituteRat, manuscriptNormV3_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_10Interval.1 manuscriptNormV3_10Interval.2 manuscriptNormV3_10SubstituteRat
    (-1330194736875770427300979589 / 500000000000000000000000000000) (-2660389473751540748094483989 / 1000000000000000000000000000000) manuscriptNormV3_10Term
    manuscriptNormV3_10_exact_interval hq manuscriptNormV3_10_rounded_endpoints.1 manuscriptNormV3_10_rounded_endpoints.2
  have hw : ((-2660389473751540748094483989 / 1000000000000000000000000000000) - (-1330194736875770427300979589 / 500000000000000000000000000000) : ℚ) = (106507475189 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_11SubstituteRat_composition_error :
    |manuscriptNormV3_11Term - (manuscriptNormV3_11SubstituteRat : ℝ)| ≤ (((194161154693 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_11SubstituteRat ∈ Set.Icc manuscriptNormV3_11Interval.1 manuscriptNormV3_11Interval.2 := by
    simpa only [manuscriptNormV3_11SubstituteRat, manuscriptNormV3_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_11Interval.1 manuscriptNormV3_11Interval.2 manuscriptNormV3_11SubstituteRat
    (4185192971723380656657287637 / 1000000000000000000000000000000) (418519297172338085081844233 / 100000000000000000000000000000) manuscriptNormV3_11Term
    manuscriptNormV3_11_exact_interval hq manuscriptNormV3_11_rounded_endpoints.1 manuscriptNormV3_11_rounded_endpoints.2
  have hw : ((418519297172338085081844233 / 100000000000000000000000000000) - (4185192971723380656657287637 / 1000000000000000000000000000000) : ℚ) = (194161154693 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV3_12SubstituteRat_composition_error :
    |manuscriptNormV3_12Term - (manuscriptNormV3_12SubstituteRat : ℝ)| ≤ (((194161154693 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV3_12SubstituteRat ∈ Set.Icc manuscriptNormV3_12Interval.1 manuscriptNormV3_12Interval.2 := by
    simpa only [manuscriptNormV3_12SubstituteRat, manuscriptNormV3_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV3_12Interval.1 manuscriptNormV3_12Interval.2 manuscriptNormV3_12SubstituteRat
    (4185192971723380656657287637 / 1000000000000000000000000000000) (418519297172338085081844233 / 100000000000000000000000000000) manuscriptNormV3_12Term
    manuscriptNormV3_12_exact_interval hq manuscriptNormV3_12_rounded_endpoints.1 manuscriptNormV3_12_rounded_endpoints.2
  have hw : ((418519297172338085081844233 / 100000000000000000000000000000) - (4185192971723380656657287637 / 1000000000000000000000000000000) : ℚ) = (194161154693 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow3_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 3 (0, 0)) - (manuscriptNormVSubstituteRow3 : ℝ)| ≤ (((1834101010821 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV3_0SubstituteRat_composition_error
  have h1 := manuscriptNormV3_1SubstituteRat_composition_error
  have h2 := manuscriptNormV3_2SubstituteRat_composition_error
  have h3 := manuscriptNormV3_3SubstituteRat_composition_error
  have h4 := manuscriptNormV3_4SubstituteRat_composition_error
  have h5 := manuscriptNormV3_5SubstituteRat_composition_error
  have h6 := manuscriptNormV3_6SubstituteRat_composition_error
  have h7 := manuscriptNormV3_7SubstituteRat_composition_error
  have h8 := manuscriptNormV3_8SubstituteRat_composition_error
  have h9 := manuscriptNormV3_9SubstituteRat_composition_error
  have h10 := manuscriptNormV3_10SubstituteRat_composition_error
  have h11 := manuscriptNormV3_11SubstituteRat_composition_error
  have h12 := manuscriptNormV3_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV3_0Term + (manuscriptNormV3_1Term + (manuscriptNormV3_2Term + (manuscriptNormV3_3Term + (manuscriptNormV3_4Term + (manuscriptNormV3_5Term + (manuscriptNormV3_6Term + (manuscriptNormV3_7Term + (manuscriptNormV3_8Term + (manuscriptNormV3_9Term + (manuscriptNormV3_10Term + (manuscriptNormV3_11Term + (manuscriptNormV3_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow3 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow3
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

def manuscriptNormV3_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1)

private theorem manuscriptNormV3_0RoundedSubstituteRat_error :
    |(manuscriptNormV3_0SubstituteRat : ℝ) - (manuscriptNormV3_0RoundedSubstituteRat : ℝ)| ≤
      (((37486072475887 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (37486072475887 / 5000000000000000) (0 / 1) (1) (0) (968 / 625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((37486072475887 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((37486072475887 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1)

private theorem manuscriptNormV3_1RoundedSubstituteRat_error :
    |(manuscriptNormV3_1SubstituteRat : ℝ) - (manuscriptNormV3_1RoundedSubstituteRat : ℝ)| ≤
      (((5489604834427 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5489604834427 / 2500000000000000) (0 / 1) (1) (0) (57121 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((5489604834427 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((5489604834427 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV3_2RoundedSubstituteRat_error :
    |(manuscriptNormV3_2SubstituteRat : ℝ) - (manuscriptNormV3_2RoundedSubstituteRat : ℝ)| ≤
      (((3138879179583 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((3138879179583 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((3138879179583 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1)

private theorem manuscriptNormV3_3RoundedSubstituteRat_error :
    |(manuscriptNormV3_3SubstituteRat : ℝ) - (manuscriptNormV3_3RoundedSubstituteRat : ℝ)| ≤
      (((6082719544489 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-6082719544489 / 2500000000000000) (0 / 1) (-7) (0) (1521 / 1250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-6082719544489 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((6082719544489 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV3_4RoundedSubstituteRat_error :
    |(manuscriptNormV3_4SubstituteRat : ℝ) - (manuscriptNormV3_4RoundedSubstituteRat : ℝ)| ≤
      (((28654058117769 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((28654058117769 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((28654058117769 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV3_5RoundedSubstituteRat_error :
    |(manuscriptNormV3_5SubstituteRat : ℝ) - (manuscriptNormV3_5RoundedSubstituteRat : ℝ)| ≤
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num) (by norm_num)
  have hw : |(((33589651698169 / 5000000000000000) : ℚ) : ℝ)| + |(((1481637471433 / 156250000000000) : ℚ) : ℝ)| =
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741)

private theorem manuscriptNormV3_6RoundedSubstituteRat_error :
    |(manuscriptNormV3_6SubstituteRat : ℝ) - (manuscriptNormV3_6RoundedSubstituteRat : ℝ)| ≤
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741) (by norm_num) (by norm_num)
  have hw : |(((33589651698169 / 5000000000000000) : ℚ) : ℝ)| + |(((-1481637471433 / 156250000000000) : ℚ) : ℝ)| =
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371)

private theorem manuscriptNormV3_7RoundedSubstituteRat_error :
    |(manuscriptNormV3_7SubstituteRat : ℝ) - (manuscriptNormV3_7RoundedSubstituteRat : ℝ)| ≤
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371) (by norm_num) (by norm_num)
  have hw : |(((-19324262066907 / 2500000000000000) : ℚ) : ℝ)| + |(((37227558060581 / 5000000000000000) : ℚ) : ℝ)| =
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV3_8RoundedSubstituteRat_error :
    |(manuscriptNormV3_8SubstituteRat : ℝ) - (manuscriptNormV3_8RoundedSubstituteRat : ℝ)| ≤
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371) (by norm_num) (by norm_num)
  have hw : |(((-19324262066907 / 2500000000000000) : ℚ) : ℝ)| + |(((-37227558060581 / 5000000000000000) : ℚ) : ℝ)| =
      (((15175216438879 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629)

private theorem manuscriptNormV3_9RoundedSubstituteRat_error :
    |(manuscriptNormV3_9SubstituteRat : ℝ) - (manuscriptNormV3_9RoundedSubstituteRat : ℝ)| ≤
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629) (by norm_num) (by norm_num)
  have hw : |(((-8254198212407 / 5000000000000000) : ℚ) : ℝ)| + |(((-14689697274259 / 5000000000000000) : ℚ) : ℝ)| =
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV3_10RoundedSubstituteRat_error :
    |(manuscriptNormV3_10SubstituteRat : ℝ) - (manuscriptNormV3_10RoundedSubstituteRat : ℝ)| ≤
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num) (by norm_num)
  have hw : |(((-8254198212407 / 5000000000000000) : ℚ) : ℝ)| + |(((14689697274259 / 5000000000000000) : ℚ) : ℝ)| =
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV3_11RoundedSubstituteRat_error :
    |(manuscriptNormV3_11SubstituteRat : ℝ) - (manuscriptNormV3_11RoundedSubstituteRat : ℝ)| ≤
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837) (by norm_num) (by norm_num)
  have hw : |(((5068806760521 / 10000000000000000) : ℚ) : ℝ)| + |(((53558167558133 / 10000000000000000) : ℚ) : ℝ)| =
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV3_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV3_12RoundedSubstituteRat_error :
    |(manuscriptNormV3_12SubstituteRat : ℝ) - (manuscriptNormV3_12RoundedSubstituteRat : ℝ)| ≤
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837) (by norm_num) (by norm_num)
  have hw : |(((5068806760521 / 10000000000000000) : ℚ) : ℝ)| + |(((-53558167558133 / 10000000000000000) : ℚ) : ℝ)| =
      (((29313487159327 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow3 : ℚ :=
  manuscriptNormV3_0RoundedSubstituteRat +
    manuscriptNormV3_1RoundedSubstituteRat +
    manuscriptNormV3_2RoundedSubstituteRat +
    manuscriptNormV3_3RoundedSubstituteRat +
    manuscriptNormV3_4RoundedSubstituteRat +
    manuscriptNormV3_5RoundedSubstituteRat +
    manuscriptNormV3_6RoundedSubstituteRat +
    manuscriptNormV3_7RoundedSubstituteRat +
    manuscriptNormV3_8RoundedSubstituteRat +
    manuscriptNormV3_9RoundedSubstituteRat +
    manuscriptNormV3_10RoundedSubstituteRat +
    manuscriptNormV3_11RoundedSubstituteRat +
    manuscriptNormV3_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow3_error :
    |(manuscriptNormVSubstituteRow3 : ℝ) - (manuscriptNormVRoundedSubstituteRow3 : ℝ)| ≤
      (((12845839223987 / 125000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV3_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV3_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV3_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV3_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV3_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV3_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV3_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV3_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV3_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV3_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV3_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV3_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV3_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow3 manuscriptNormVRoundedSubstituteRow3
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

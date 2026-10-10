import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup003
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup004
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup005
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup006
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP1_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP1_0SubstituteRat_interval :
    manuscriptNormP1_0SubstituteRat ∈ Set.Icc manuscriptNormP1_0Interval.1 manuscriptNormP1_0Interval.2 := by
  simpa only [manuscriptNormP1_0SubstituteRat, manuscriptNormP1_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormP1_0SubstituteRat_upper :
    manuscriptNormP1_0SubstituteRat ≤ (3208640661093686384636201629 / 1000000000000000000000000000000) :=
  manuscriptNormP1_0SubstituteRat_interval.2.trans manuscriptNormP1_0_rounded_endpoints.2

def manuscriptNormP1_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1)

private theorem manuscriptNormP1_1SubstituteRat_interval :
    manuscriptNormP1_1SubstituteRat ∈ Set.Icc manuscriptNormP1_1Interval.1 manuscriptNormP1_1Interval.2 := by
  simpa only [manuscriptNormP1_1SubstituteRat, manuscriptNormP1_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormP1_1SubstituteRat_upper :
    manuscriptNormP1_1SubstituteRat ≤ (246583631505083683242477679 / 250000000000000000000000000000) :=
  manuscriptNormP1_1SubstituteRat_interval.2.trans manuscriptNormP1_1_rounded_endpoints.2

def manuscriptNormP1_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP1_2SubstituteRat_interval :
    manuscriptNormP1_2SubstituteRat ∈ Set.Icc manuscriptNormP1_2Interval.1 manuscriptNormP1_2Interval.2 := by
  simpa only [manuscriptNormP1_2SubstituteRat, manuscriptNormP1_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num))

private theorem manuscriptNormP1_2SubstituteRat_upper :
    manuscriptNormP1_2SubstituteRat ≤ (711831734440164842505553349 / 1000000000000000000000000000000) :=
  manuscriptNormP1_2SubstituteRat_interval.2.trans manuscriptNormP1_2_rounded_endpoints.2

def manuscriptNormP1_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829)

private theorem manuscriptNormP1_3SubstituteRat_interval :
    manuscriptNormP1_3SubstituteRat ∈ Set.Icc manuscriptNormP1_3Interval.1 manuscriptNormP1_3Interval.2 := by
  simpa only [manuscriptNormP1_3SubstituteRat, manuscriptNormP1_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829) (by norm_num))

private theorem manuscriptNormP1_3SubstituteRat_upper :
    manuscriptNormP1_3SubstituteRat ≤ (711831734440164842505553349 / 1000000000000000000000000000000) :=
  manuscriptNormP1_3SubstituteRat_interval.2.trans manuscriptNormP1_3_rounded_endpoints.2

def manuscriptNormP1_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP1_4SubstituteRat_interval :
    manuscriptNormP1_4SubstituteRat ∈ Set.Icc manuscriptNormP1_4Interval.1 manuscriptNormP1_4Interval.2 := by
  simpa only [manuscriptNormP1_4SubstituteRat, manuscriptNormP1_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num))

private theorem manuscriptNormP1_4SubstituteRat_upper :
    manuscriptNormP1_4SubstituteRat ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) :=
  manuscriptNormP1_4SubstituteRat_interval.2.trans manuscriptNormP1_4_rounded_endpoints.2

def manuscriptNormP1_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP1_5SubstituteRat_interval :
    manuscriptNormP1_5SubstituteRat ∈ Set.Icc manuscriptNormP1_5Interval.1 manuscriptNormP1_5Interval.2 := by
  simpa only [manuscriptNormP1_5SubstituteRat, manuscriptNormP1_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num))

private theorem manuscriptNormP1_5SubstituteRat_upper :
    manuscriptNormP1_5SubstituteRat ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) :=
  manuscriptNormP1_5SubstituteRat_interval.2.trans manuscriptNormP1_5_rounded_endpoints.2

def manuscriptNormP1_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP1_6SubstituteRat_interval :
    manuscriptNormP1_6SubstituteRat ∈ Set.Icc manuscriptNormP1_6Interval.1 manuscriptNormP1_6Interval.2 := by
  simpa only [manuscriptNormP1_6SubstituteRat, manuscriptNormP1_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num))

private theorem manuscriptNormP1_6SubstituteRat_upper :
    manuscriptNormP1_6SubstituteRat ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) :=
  manuscriptNormP1_6SubstituteRat_interval.2.trans manuscriptNormP1_6_rounded_endpoints.2

def manuscriptNormP1_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229)

private theorem manuscriptNormP1_7SubstituteRat_interval :
    manuscriptNormP1_7SubstituteRat ∈ Set.Icc manuscriptNormP1_7Interval.1 manuscriptNormP1_7Interval.2 := by
  simpa only [manuscriptNormP1_7SubstituteRat, manuscriptNormP1_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229) (by norm_num))

private theorem manuscriptNormP1_7SubstituteRat_upper :
    manuscriptNormP1_7SubstituteRat ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) :=
  manuscriptNormP1_7SubstituteRat_interval.2.trans manuscriptNormP1_7_rounded_endpoints.2

def manuscriptNormP1_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP1_8SubstituteRat_interval :
    manuscriptNormP1_8SubstituteRat ∈ Set.Icc manuscriptNormP1_8Interval.1 manuscriptNormP1_8Interval.2 := by
  simpa only [manuscriptNormP1_8SubstituteRat, manuscriptNormP1_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num))

private theorem manuscriptNormP1_8SubstituteRat_upper :
    manuscriptNormP1_8SubstituteRat ≤ (580408182566126009652303041 / 1000000000000000000000000000000) :=
  manuscriptNormP1_8SubstituteRat_interval.2.trans manuscriptNormP1_8_rounded_endpoints.2

def manuscriptNormP1_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391)

private theorem manuscriptNormP1_9SubstituteRat_interval :
    manuscriptNormP1_9SubstituteRat ∈ Set.Icc manuscriptNormP1_9Interval.1 manuscriptNormP1_9Interval.2 := by
  simpa only [manuscriptNormP1_9SubstituteRat, manuscriptNormP1_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391) (by norm_num))

private theorem manuscriptNormP1_9SubstituteRat_upper :
    manuscriptNormP1_9SubstituteRat ≤ (580408182566126009652303041 / 1000000000000000000000000000000) :=
  manuscriptNormP1_9SubstituteRat_interval.2.trans manuscriptNormP1_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow1 : ℚ :=
  manuscriptNormP1_0SubstituteRat +
    manuscriptNormP1_1SubstituteRat +
    manuscriptNormP1_2SubstituteRat +
    manuscriptNormP1_3SubstituteRat +
    manuscriptNormP1_4SubstituteRat +
    manuscriptNormP1_5SubstituteRat +
    manuscriptNormP1_6SubstituteRat +
    manuscriptNormP1_7SubstituteRat +
    manuscriptNormP1_8SubstituteRat +
    manuscriptNormP1_9SubstituteRat

theorem manuscriptNormPSubstituteRow1_upper : manuscriptNormPSubstituteRow1 ≤ (4239937178462756377151314421 / 1000000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow1
  linarith only [manuscriptNormP1_0SubstituteRat_upper,
    manuscriptNormP1_1SubstituteRat_upper,
    manuscriptNormP1_2SubstituteRat_upper,
    manuscriptNormP1_3SubstituteRat_upper,
    manuscriptNormP1_4SubstituteRat_upper,
    manuscriptNormP1_5SubstituteRat_upper,
    manuscriptNormP1_6SubstituteRat_upper,
    manuscriptNormP1_7SubstituteRat_upper,
    manuscriptNormP1_8SubstituteRat_upper,
    manuscriptNormP1_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP1_0SubstituteRat_composition_error :
    |manuscriptNormP1_0Term - (manuscriptNormP1_0SubstituteRat : ℝ)| ≤ (((168798733 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_0SubstituteRat ∈ Set.Icc manuscriptNormP1_0Interval.1 manuscriptNormP1_0Interval.2 := by
    simpa only [manuscriptNormP1_0SubstituteRat, manuscriptNormP1_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_0Interval.1 manuscriptNormP1_0Interval.2 manuscriptNormP1_0SubstituteRat
    (3208640661093686383961006697 / 1000000000000000000000000000000) (3208640661093686384636201629 / 1000000000000000000000000000000) manuscriptNormP1_0Term
    manuscriptNormP1_0_exact_interval hq manuscriptNormP1_0_rounded_endpoints.1 manuscriptNormP1_0_rounded_endpoints.2
  have hw : ((3208640661093686384636201629 / 1000000000000000000000000000000) - (3208640661093686383961006697 / 1000000000000000000000000000000) : ℚ) = (168798733 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_1SubstituteRat_composition_error :
    |manuscriptNormP1_1Term - (manuscriptNormP1_1SubstituteRat : ℝ)| ≤ (((216781503 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_1SubstituteRat ∈ Set.Icc manuscriptNormP1_1Interval.1 manuscriptNormP1_1Interval.2 := by
    simpa only [manuscriptNormP1_1SubstituteRat, manuscriptNormP1_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_1Interval.1 manuscriptNormP1_1Interval.2 manuscriptNormP1_1SubstituteRat
    (986334526020334732753129213 / 1000000000000000000000000000000) (246583631505083683242477679 / 250000000000000000000000000000) manuscriptNormP1_1Term
    manuscriptNormP1_1_exact_interval hq manuscriptNormP1_1_rounded_endpoints.1 manuscriptNormP1_1_rounded_endpoints.2
  have hw : ((246583631505083683242477679 / 250000000000000000000000000000) - (986334526020334732753129213 / 1000000000000000000000000000000) : ℚ) = (216781503 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_2SubstituteRat_composition_error :
    |manuscriptNormP1_2Term - (manuscriptNormP1_2SubstituteRat : ℝ)| ≤ (((123856202107 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_2SubstituteRat ∈ Set.Icc manuscriptNormP1_2Interval.1 manuscriptNormP1_2Interval.2 := by
    simpa only [manuscriptNormP1_2SubstituteRat, manuscriptNormP1_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_2Interval.1 manuscriptNormP1_2Interval.2 manuscriptNormP1_2SubstituteRat
    (355915867220082359324675621 / 500000000000000000000000000000) (711831734440164842505553349 / 1000000000000000000000000000000) manuscriptNormP1_2Term
    manuscriptNormP1_2_exact_interval hq manuscriptNormP1_2_rounded_endpoints.1 manuscriptNormP1_2_rounded_endpoints.2
  have hw : ((711831734440164842505553349 / 1000000000000000000000000000000) - (355915867220082359324675621 / 500000000000000000000000000000) : ℚ) = (123856202107 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_3SubstituteRat_composition_error :
    |manuscriptNormP1_3Term - (manuscriptNormP1_3SubstituteRat : ℝ)| ≤ (((123856202107 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_3SubstituteRat ∈ Set.Icc manuscriptNormP1_3Interval.1 manuscriptNormP1_3Interval.2 := by
    simpa only [manuscriptNormP1_3SubstituteRat, manuscriptNormP1_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_3Interval.1 manuscriptNormP1_3Interval.2 manuscriptNormP1_3SubstituteRat
    (355915867220082359324675621 / 500000000000000000000000000000) (711831734440164842505553349 / 1000000000000000000000000000000) manuscriptNormP1_3Term
    manuscriptNormP1_3_exact_interval hq manuscriptNormP1_3_rounded_endpoints.1 manuscriptNormP1_3_rounded_endpoints.2
  have hw : ((711831734440164842505553349 / 1000000000000000000000000000000) - (355915867220082359324675621 / 500000000000000000000000000000) : ℚ) = (123856202107 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_4SubstituteRat_composition_error :
    |manuscriptNormP1_4Term - (manuscriptNormP1_4SubstituteRat : ℝ)| ≤ (((11650289219 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_4SubstituteRat ∈ Set.Icc manuscriptNormP1_4Interval.1 manuscriptNormP1_4Interval.2 := by
    simpa only [manuscriptNormP1_4SubstituteRat, manuscriptNormP1_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_4Interval.1 manuscriptNormP1_4Interval.2 manuscriptNormP1_4SubstituteRat
    (-465843978124225478021104641 / 1000000000000000000000000000000) (-465843978124225454720526203 / 1000000000000000000000000000000) manuscriptNormP1_4Term
    manuscriptNormP1_4_exact_interval hq manuscriptNormP1_4_rounded_endpoints.1 manuscriptNormP1_4_rounded_endpoints.2
  have hw : ((-465843978124225454720526203 / 1000000000000000000000000000000) - (-465843978124225478021104641 / 1000000000000000000000000000000) : ℚ) = (11650289219 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_5SubstituteRat_composition_error :
    |manuscriptNormP1_5Term - (manuscriptNormP1_5SubstituteRat : ℝ)| ≤ (((11650289219 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_5SubstituteRat ∈ Set.Icc manuscriptNormP1_5Interval.1 manuscriptNormP1_5Interval.2 := by
    simpa only [manuscriptNormP1_5SubstituteRat, manuscriptNormP1_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_5Interval.1 manuscriptNormP1_5Interval.2 manuscriptNormP1_5SubstituteRat
    (-465843978124225478021104641 / 1000000000000000000000000000000) (-465843978124225454720526203 / 1000000000000000000000000000000) manuscriptNormP1_5Term
    manuscriptNormP1_5_exact_interval hq manuscriptNormP1_5_rounded_endpoints.1 manuscriptNormP1_5_rounded_endpoints.2
  have hw : ((-465843978124225454720526203 / 1000000000000000000000000000000) - (-465843978124225478021104641 / 1000000000000000000000000000000) : ℚ) = (11650289219 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_6SubstituteRat_composition_error :
    |manuscriptNormP1_6Term - (manuscriptNormP1_6SubstituteRat : ℝ)| ≤ (((34656891447 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_6SubstituteRat ∈ Set.Icc manuscriptNormP1_6Interval.1 manuscriptNormP1_6Interval.2 := by
    simpa only [manuscriptNormP1_6SubstituteRat, manuscriptNormP1_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_6Interval.1 manuscriptNormP1_6Interval.2 manuscriptNormP1_6SubstituteRat
    (-200978735801924450580405149 / 250000000000000000000000000000) (-803914943207697767664729149 / 1000000000000000000000000000000) manuscriptNormP1_6Term
    manuscriptNormP1_6_exact_interval hq manuscriptNormP1_6_rounded_endpoints.1 manuscriptNormP1_6_rounded_endpoints.2
  have hw : ((-803914943207697767664729149 / 1000000000000000000000000000000) - (-200978735801924450580405149 / 250000000000000000000000000000) : ℚ) = (34656891447 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_7SubstituteRat_composition_error :
    |manuscriptNormP1_7Term - (manuscriptNormP1_7SubstituteRat : ℝ)| ≤ (((34656891447 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_7SubstituteRat ∈ Set.Icc manuscriptNormP1_7Interval.1 manuscriptNormP1_7Interval.2 := by
    simpa only [manuscriptNormP1_7SubstituteRat, manuscriptNormP1_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_7Interval.1 manuscriptNormP1_7Interval.2 manuscriptNormP1_7SubstituteRat
    (-200978735801924450580405149 / 250000000000000000000000000000) (-803914943207697767664729149 / 1000000000000000000000000000000) manuscriptNormP1_7Term
    manuscriptNormP1_7_exact_interval hq manuscriptNormP1_7_rounded_endpoints.1 manuscriptNormP1_7_rounded_endpoints.2
  have hw : ((-803914943207697767664729149 / 1000000000000000000000000000000) - (-200978735801924450580405149 / 250000000000000000000000000000) : ℚ) = (34656891447 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_8SubstituteRat_composition_error :
    |manuscriptNormP1_8Term - (manuscriptNormP1_8SubstituteRat : ℝ)| ≤ (((35292165581 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_8SubstituteRat ∈ Set.Icc manuscriptNormP1_8Interval.1 manuscriptNormP1_8Interval.2 := by
    simpa only [manuscriptNormP1_8SubstituteRat, manuscriptNormP1_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_8Interval.1 manuscriptNormP1_8Interval.2 manuscriptNormP1_8SubstituteRat
    (29020409128306298718006873 / 50000000000000000000000000000) (580408182566126009652303041 / 1000000000000000000000000000000) manuscriptNormP1_8Term
    manuscriptNormP1_8_exact_interval hq manuscriptNormP1_8_rounded_endpoints.1 manuscriptNormP1_8_rounded_endpoints.2
  have hw : ((580408182566126009652303041 / 1000000000000000000000000000000) - (29020409128306298718006873 / 50000000000000000000000000000) : ℚ) = (35292165581 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP1_9SubstituteRat_composition_error :
    |manuscriptNormP1_9Term - (manuscriptNormP1_9SubstituteRat : ℝ)| ≤ (((35292165581 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP1_9SubstituteRat ∈ Set.Icc manuscriptNormP1_9Interval.1 manuscriptNormP1_9Interval.2 := by
    simpa only [manuscriptNormP1_9SubstituteRat, manuscriptNormP1_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP1_9Interval.1 manuscriptNormP1_9Interval.2 manuscriptNormP1_9SubstituteRat
    (29020409128306298718006873 / 50000000000000000000000000000) (580408182566126009652303041 / 1000000000000000000000000000000) manuscriptNormP1_9Term
    manuscriptNormP1_9_exact_interval hq manuscriptNormP1_9_rounded_endpoints.1 manuscriptNormP1_9_rounded_endpoints.2
  have hw : ((580408182566126009652303041 / 1000000000000000000000000000000) - (29020409128306298718006873 / 50000000000000000000000000000) : ℚ) = (35292165581 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow1_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 1 (0, 0)) - (manuscriptNormPSubstituteRow1 : ℝ)| ≤ (((435103651581 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP1_0SubstituteRat_composition_error
  have h1 := manuscriptNormP1_1SubstituteRat_composition_error
  have h2 := manuscriptNormP1_2SubstituteRat_composition_error
  have h3 := manuscriptNormP1_3SubstituteRat_composition_error
  have h4 := manuscriptNormP1_4SubstituteRat_composition_error
  have h5 := manuscriptNormP1_5SubstituteRat_composition_error
  have h6 := manuscriptNormP1_6SubstituteRat_composition_error
  have h7 := manuscriptNormP1_7SubstituteRat_composition_error
  have h8 := manuscriptNormP1_8SubstituteRat_composition_error
  have h9 := manuscriptNormP1_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP1_0Term + (manuscriptNormP1_1Term + (manuscriptNormP1_2Term + (manuscriptNormP1_3Term + (manuscriptNormP1_4Term + (manuscriptNormP1_5Term + (manuscriptNormP1_6Term + (manuscriptNormP1_7Term + (manuscriptNormP1_8Term + (manuscriptNormP1_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow1 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow1
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
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptNormP1_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP1_0RoundedSubstituteRat_error :
    |(manuscriptNormP1_0SubstituteRat : ℝ) - (manuscriptNormP1_0RoundedSubstituteRat : ℝ)| ≤
      (((4999594751017 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-4999594751017 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((4999594751017 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1)

private theorem manuscriptNormP1_1RoundedSubstituteRat_error :
    |(manuscriptNormP1_1SubstituteRat : ℝ) - (manuscriptNormP1_1RoundedSubstituteRat : ℝ)| ≤
      (((4586060797081 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-4586060797081 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((4586060797081 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP1_2RoundedSubstituteRat_error :
    |(manuscriptNormP1_2SubstituteRat : ℝ) - (manuscriptNormP1_2RoundedSubstituteRat : ℝ)| ≤
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829) (by norm_num) (by norm_num)
  have hw : |(((-70967383232149 / 10000000000000000) : ℚ) : ℝ)| + |(((68330346181621 / 20000000000000000) : ℚ) : ℝ)| =
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829)

private theorem manuscriptNormP1_3RoundedSubstituteRat_error :
    |(manuscriptNormP1_3SubstituteRat : ℝ) - (manuscriptNormP1_3RoundedSubstituteRat : ℝ)| ≤
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829) (by norm_num) (by norm_num)
  have hw : |(((-70967383232149 / 10000000000000000) : ℚ) : ℝ)| + |(((-68330346181621 / 20000000000000000) : ℚ) : ℝ)| =
      (((210265112645919 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP1_4RoundedSubstituteRat_error :
    |(manuscriptNormP1_4SubstituteRat : ℝ) - (manuscriptNormP1_4RoundedSubstituteRat : ℝ)| ≤
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num) (by norm_num)
  have hw : |(((-2637591701359 / 20000000000000000) : ℚ) : ℝ)| + |(((-2570943658261 / 4000000000000000) : ℚ) : ℝ)| =
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP1_5RoundedSubstituteRat_error :
    |(manuscriptNormP1_5SubstituteRat : ℝ) - (manuscriptNormP1_5RoundedSubstituteRat : ℝ)| ≤
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num) (by norm_num)
  have hw : |(((-2637591701359 / 20000000000000000) : ℚ) : ℝ)| + |(((2570943658261 / 4000000000000000) : ℚ) : ℝ)| =
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP1_6RoundedSubstituteRat_error :
    |(manuscriptNormP1_6SubstituteRat : ℝ) - (manuscriptNormP1_6RoundedSubstituteRat : ℝ)| ≤
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num) (by norm_num)
  have hw : |(((-3454166215131 / 10000000000000000) : ℚ) : ℝ)| + |(((-9559946732553 / 10000000000000000) : ℚ) : ℝ)| =
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229)

private theorem manuscriptNormP1_7RoundedSubstituteRat_error :
    |(manuscriptNormP1_7SubstituteRat : ℝ) - (manuscriptNormP1_7RoundedSubstituteRat : ℝ)| ≤
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229) (by norm_num) (by norm_num)
  have hw : |(((-3454166215131 / 10000000000000000) : ℚ) : ℝ)| + |(((9559946732553 / 10000000000000000) : ℚ) : ℝ)| =
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP1_8RoundedSubstituteRat_error :
    |(manuscriptNormP1_8SubstituteRat : ℝ) - (manuscriptNormP1_8RoundedSubstituteRat : ℝ)| ≤
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num) (by norm_num)
  have hw : |(((-70453504591 / 312500000000000) : ℚ) : ℝ)| + |(((19469072932083 / 20000000000000000) : ℚ) : ℝ)| =
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP1_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391)

private theorem manuscriptNormP1_9RoundedSubstituteRat_error :
    |(manuscriptNormP1_9SubstituteRat : ℝ) - (manuscriptNormP1_9RoundedSubstituteRat : ℝ)| ≤
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391) (by norm_num) (by norm_num)
  have hw : |(((-70453504591 / 312500000000000) : ℚ) : ℝ)| + |(((-19469072932083 / 20000000000000000) : ℚ) : ℝ)| =
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow1 : ℚ :=
  manuscriptNormP1_0RoundedSubstituteRat +
    manuscriptNormP1_1RoundedSubstituteRat +
    manuscriptNormP1_2RoundedSubstituteRat +
    manuscriptNormP1_3RoundedSubstituteRat +
    manuscriptNormP1_4RoundedSubstituteRat +
    manuscriptNormP1_5RoundedSubstituteRat +
    manuscriptNormP1_6RoundedSubstituteRat +
    manuscriptNormP1_7RoundedSubstituteRat +
    manuscriptNormP1_8RoundedSubstituteRat +
    manuscriptNormP1_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow1_error :
    |(manuscriptNormPSubstituteRow1 : ℝ) - (manuscriptNormPRoundedSubstituteRow1 : ℝ)| ≤
      (((300348185561007 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP1_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP1_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP1_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP1_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP1_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP1_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP1_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP1_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP1_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP1_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow1 manuscriptNormPRoundedSubstituteRow1
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
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
    (abs_le.mp h9).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2]

end InternalCatalan

end

end

end OAI

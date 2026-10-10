import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup016
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup017
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup018
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup019
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP5_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP5_0SubstituteRat_interval :
    manuscriptNormP5_0SubstituteRat ∈ Set.Icc manuscriptNormP5_0Interval.1 manuscriptNormP5_0Interval.2 := by
  simpa only [manuscriptNormP5_0SubstituteRat, manuscriptNormP5_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num))

private theorem manuscriptNormP5_0SubstituteRat_upper :
    manuscriptNormP5_0SubstituteRat ≤ (-117148695045692465091096139 / 62500000000000000000000000000) :=
  manuscriptNormP5_0SubstituteRat_interval.2.trans manuscriptNormP5_0_rounded_endpoints.2

def manuscriptNormP5_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP5_1SubstituteRat_interval :
    manuscriptNormP5_1SubstituteRat ∈ Set.Icc manuscriptNormP5_1Interval.1 manuscriptNormP5_1Interval.2 := by
  simpa only [manuscriptNormP5_1SubstituteRat, manuscriptNormP5_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num))

private theorem manuscriptNormP5_1SubstituteRat_upper :
    manuscriptNormP5_1SubstituteRat ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) :=
  manuscriptNormP5_1SubstituteRat_interval.2.trans manuscriptNormP5_1_rounded_endpoints.2

def manuscriptNormP5_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP5_2SubstituteRat_interval :
    manuscriptNormP5_2SubstituteRat ∈ Set.Icc manuscriptNormP5_2Interval.1 manuscriptNormP5_2Interval.2 := by
  simpa only [manuscriptNormP5_2SubstituteRat, manuscriptNormP5_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))

private theorem manuscriptNormP5_2SubstituteRat_upper :
    manuscriptNormP5_2SubstituteRat ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) :=
  manuscriptNormP5_2SubstituteRat_interval.2.trans manuscriptNormP5_2_rounded_endpoints.2

def manuscriptNormP5_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP5_3SubstituteRat_interval :
    manuscriptNormP5_3SubstituteRat ∈ Set.Icc manuscriptNormP5_3Interval.1 manuscriptNormP5_3Interval.2 := by
  simpa only [manuscriptNormP5_3SubstituteRat, manuscriptNormP5_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))

private theorem manuscriptNormP5_3SubstituteRat_upper :
    manuscriptNormP5_3SubstituteRat ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) :=
  manuscriptNormP5_3SubstituteRat_interval.2.trans manuscriptNormP5_3_rounded_endpoints.2

def manuscriptNormP5_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP5_4SubstituteRat_interval :
    manuscriptNormP5_4SubstituteRat ∈ Set.Icc manuscriptNormP5_4Interval.1 manuscriptNormP5_4Interval.2 := by
  simpa only [manuscriptNormP5_4SubstituteRat, manuscriptNormP5_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))

private theorem manuscriptNormP5_4SubstituteRat_upper :
    manuscriptNormP5_4SubstituteRat ≤ (1203374562608596014442386537 / 1000000000000000000000000000000) :=
  manuscriptNormP5_4SubstituteRat_interval.2.trans manuscriptNormP5_4_rounded_endpoints.2

def manuscriptNormP5_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP5_5SubstituteRat_interval :
    manuscriptNormP5_5SubstituteRat ∈ Set.Icc manuscriptNormP5_5Interval.1 manuscriptNormP5_5Interval.2 := by
  simpa only [manuscriptNormP5_5SubstituteRat, manuscriptNormP5_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num))

private theorem manuscriptNormP5_5SubstituteRat_upper :
    manuscriptNormP5_5SubstituteRat ≤ (469208388071489204645537183 / 1000000000000000000000000000000) :=
  manuscriptNormP5_5SubstituteRat_interval.2.trans manuscriptNormP5_5_rounded_endpoints.2

def manuscriptNormP5_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP5_6SubstituteRat_interval :
    manuscriptNormP5_6SubstituteRat ∈ Set.Icc manuscriptNormP5_6Interval.1 manuscriptNormP5_6Interval.2 := by
  simpa only [manuscriptNormP5_6SubstituteRat, manuscriptNormP5_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))

private theorem manuscriptNormP5_6SubstituteRat_upper :
    manuscriptNormP5_6SubstituteRat ≤ (1016528929435293007022945239 / 500000000000000000000000000000) :=
  manuscriptNormP5_6SubstituteRat_interval.2.trans manuscriptNormP5_6_rounded_endpoints.2

def manuscriptNormP5_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP5_7SubstituteRat_interval :
    manuscriptNormP5_7SubstituteRat ∈ Set.Icc manuscriptNormP5_7Interval.1 manuscriptNormP5_7Interval.2 := by
  simpa only [manuscriptNormP5_7SubstituteRat, manuscriptNormP5_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))

private theorem manuscriptNormP5_7SubstituteRat_upper :
    manuscriptNormP5_7SubstituteRat ≤ (1095337454857858872694069 / 1600000000000000000000000000) :=
  manuscriptNormP5_7SubstituteRat_interval.2.trans manuscriptNormP5_7_rounded_endpoints.2

def manuscriptNormP5_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP5_8SubstituteRat_interval :
    manuscriptNormP5_8SubstituteRat ∈ Set.Icc manuscriptNormP5_8Interval.1 manuscriptNormP5_8Interval.2 := by
  simpa only [manuscriptNormP5_8SubstituteRat, manuscriptNormP5_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))

private theorem manuscriptNormP5_8SubstituteRat_upper :
    manuscriptNormP5_8SubstituteRat ≤ (-1695532107765573584766603021 / 1000000000000000000000000000000) :=
  manuscriptNormP5_8SubstituteRat_interval.2.trans manuscriptNormP5_8_rounded_endpoints.2

def manuscriptNormP5_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP5_9SubstituteRat_interval :
    manuscriptNormP5_9SubstituteRat ∈ Set.Icc manuscriptNormP5_9Interval.1 manuscriptNormP5_9Interval.2 := by
  simpa only [manuscriptNormP5_9SubstituteRat, manuscriptNormP5_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))

private theorem manuscriptNormP5_9SubstituteRat_upper :
    manuscriptNormP5_9SubstituteRat ≤ (-412726265283760513035682481 / 500000000000000000000000000000) :=
  manuscriptNormP5_9SubstituteRat_interval.2.trans manuscriptNormP5_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow5 : ℚ :=
  manuscriptNormP5_0SubstituteRat +
    manuscriptNormP5_1SubstituteRat +
    manuscriptNormP5_2SubstituteRat +
    manuscriptNormP5_3SubstituteRat +
    manuscriptNormP5_4SubstituteRat +
    manuscriptNormP5_5SubstituteRat +
    manuscriptNormP5_6SubstituteRat +
    manuscriptNormP5_7SubstituteRat +
    manuscriptNormP5_8SubstituteRat +
    manuscriptNormP5_9SubstituteRat

theorem manuscriptNormPSubstituteRow5_upper : manuscriptNormPSubstituteRow5 ≤ (-307130964255497237530195231 / 50000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow5
  linarith only [manuscriptNormP5_0SubstituteRat_upper,
    manuscriptNormP5_1SubstituteRat_upper,
    manuscriptNormP5_2SubstituteRat_upper,
    manuscriptNormP5_3SubstituteRat_upper,
    manuscriptNormP5_4SubstituteRat_upper,
    manuscriptNormP5_5SubstituteRat_upper,
    manuscriptNormP5_6SubstituteRat_upper,
    manuscriptNormP5_7SubstituteRat_upper,
    manuscriptNormP5_8SubstituteRat_upper,
    manuscriptNormP5_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP5_0SubstituteRat_composition_error :
    |manuscriptNormP5_0Term - (manuscriptNormP5_0SubstituteRat : ℝ)| ≤ (((101606546013 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_0SubstituteRat ∈ Set.Icc manuscriptNormP5_0Interval.1 manuscriptNormP5_0Interval.2 := by
    simpa only [manuscriptNormP5_0SubstituteRat, manuscriptNormP5_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_0Interval.1 manuscriptNormP5_0Interval.2 manuscriptNormP5_0SubstituteRat
    (-1874379120731079543064084237 / 1000000000000000000000000000000) (-117148695045692465091096139 / 62500000000000000000000000000) manuscriptNormP5_0Term
    manuscriptNormP5_0_exact_interval hq manuscriptNormP5_0_rounded_endpoints.1 manuscriptNormP5_0_rounded_endpoints.2
  have hw : ((-117148695045692465091096139 / 62500000000000000000000000000) - (-1874379120731079543064084237 / 1000000000000000000000000000000) : ℚ) = (101606546013 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_1SubstituteRat_composition_error :
    |manuscriptNormP5_1Term - (manuscriptNormP5_1SubstituteRat : ℝ)| ≤ (((11650289219 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_1SubstituteRat ∈ Set.Icc manuscriptNormP5_1Interval.1 manuscriptNormP5_1Interval.2 := by
    simpa only [manuscriptNormP5_1SubstituteRat, manuscriptNormP5_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_1Interval.1 manuscriptNormP5_1Interval.2 manuscriptNormP5_1SubstituteRat
    (-465843978124225478021104641 / 1000000000000000000000000000000) (-465843978124225454720526203 / 1000000000000000000000000000000) manuscriptNormP5_1Term
    manuscriptNormP5_1_exact_interval hq manuscriptNormP5_1_rounded_endpoints.1 manuscriptNormP5_1_rounded_endpoints.2
  have hw : ((-465843978124225454720526203 / 1000000000000000000000000000000) - (-465843978124225478021104641 / 1000000000000000000000000000000) : ℚ) = (11650289219 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_2SubstituteRat_composition_error :
    |manuscriptNormP5_2Term - (manuscriptNormP5_2SubstituteRat : ℝ)| ≤ (((278283571 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_2SubstituteRat ∈ Set.Icc manuscriptNormP5_2Interval.1 manuscriptNormP5_2Interval.2 := by
    simpa only [manuscriptNormP5_2SubstituteRat, manuscriptNormP5_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_2Interval.1 manuscriptNormP5_2Interval.2 manuscriptNormP5_2SubstituteRat
    (-620836233685038813724759441 / 250000000000000000000000000000) (-1241672467370077627171235311 / 500000000000000000000000000000) manuscriptNormP5_2Term
    manuscriptNormP5_2_exact_interval hq manuscriptNormP5_2_rounded_endpoints.1 manuscriptNormP5_2_rounded_endpoints.2
  have hw : ((-1241672467370077627171235311 / 500000000000000000000000000000) - (-620836233685038813724759441 / 250000000000000000000000000000) : ℚ) = (278283571 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_3SubstituteRat_composition_error :
    |manuscriptNormP5_3Term - (manuscriptNormP5_3SubstituteRat : ℝ)| ≤ (((230564907 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_3SubstituteRat ∈ Set.Icc manuscriptNormP5_3Interval.1 manuscriptNormP5_3Interval.2 := by
    simpa only [manuscriptNormP5_3SubstituteRat, manuscriptNormP5_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_3Interval.1 manuscriptNormP5_3Interval.2 manuscriptNormP5_3SubstituteRat
    (-127531733280728920730965549 / 40000000000000000000000000000) (-3188293332018223017813008911 / 1000000000000000000000000000000) manuscriptNormP5_3Term
    manuscriptNormP5_3_exact_interval hq manuscriptNormP5_3_rounded_endpoints.1 manuscriptNormP5_3_rounded_endpoints.2
  have hw : ((-3188293332018223017813008911 / 1000000000000000000000000000000) - (-127531733280728920730965549 / 40000000000000000000000000000) : ℚ) = (230564907 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_4SubstituteRat_composition_error :
    |manuscriptNormP5_4Term - (manuscriptNormP5_4SubstituteRat : ℝ)| ≤ (((50709509 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_4SubstituteRat ∈ Set.Icc manuscriptNormP5_4Interval.1 manuscriptNormP5_4Interval.2 := by
    simpa only [manuscriptNormP5_4SubstituteRat, manuscriptNormP5_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_4Interval.1 manuscriptNormP5_4Interval.2 manuscriptNormP5_4SubstituteRat
    (75210910163037250886802437 / 62500000000000000000000000000) (1203374562608596014442386537 / 1000000000000000000000000000000) manuscriptNormP5_4Term
    manuscriptNormP5_4_exact_interval hq manuscriptNormP5_4_rounded_endpoints.1 manuscriptNormP5_4_rounded_endpoints.2
  have hw : ((1203374562608596014442386537 / 1000000000000000000000000000000) - (75210910163037250886802437 / 62500000000000000000000000000) : ℚ) = (50709509 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_5SubstituteRat_composition_error :
    |manuscriptNormP5_5Term - (manuscriptNormP5_5SubstituteRat : ℝ)| ≤ (((1456631 / 25000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_5SubstituteRat ∈ Set.Icc manuscriptNormP5_5Interval.1 manuscriptNormP5_5Interval.2 := by
    simpa only [manuscriptNormP5_5SubstituteRat, manuscriptNormP5_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_5Interval.1 manuscriptNormP5_5Interval.2 manuscriptNormP5_5SubstituteRat
    (469208388071489204587271943 / 1000000000000000000000000000000) (469208388071489204645537183 / 1000000000000000000000000000000) manuscriptNormP5_5Term
    manuscriptNormP5_5_exact_interval hq manuscriptNormP5_5_rounded_endpoints.1 manuscriptNormP5_5_rounded_endpoints.2
  have hw : ((469208388071489204645537183 / 1000000000000000000000000000000) - (469208388071489204587271943 / 1000000000000000000000000000000) : ℚ) = (1456631 / 25000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_6SubstituteRat_composition_error :
    |manuscriptNormP5_6Term - (manuscriptNormP5_6SubstituteRat : ℝ)| ≤ (((97182271 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_6SubstituteRat ∈ Set.Icc manuscriptNormP5_6Interval.1 manuscriptNormP5_6Interval.2 := by
    simpa only [manuscriptNormP5_6SubstituteRat, manuscriptNormP5_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_6Interval.1 manuscriptNormP5_6Interval.2 manuscriptNormP5_6SubstituteRat
    (2033057858870586013559979123 / 1000000000000000000000000000000) (1016528929435293007022945239 / 500000000000000000000000000000) manuscriptNormP5_6Term
    manuscriptNormP5_6_exact_interval hq manuscriptNormP5_6_rounded_endpoints.1 manuscriptNormP5_6_rounded_endpoints.2
  have hw : ((1016528929435293007022945239 / 500000000000000000000000000000) - (2033057858870586013559979123 / 1000000000000000000000000000000) : ℚ) = (97182271 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_7SubstituteRat_composition_error :
    |manuscriptNormP5_7Term - (manuscriptNormP5_7SubstituteRat : ℝ)| ≤ (((8376447 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_7SubstituteRat ∈ Set.Icc manuscriptNormP5_7Interval.1 manuscriptNormP5_7Interval.2 := by
    simpa only [manuscriptNormP5_7SubstituteRat, manuscriptNormP5_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_7Interval.1 manuscriptNormP5_7Interval.2 manuscriptNormP5_7SubstituteRat
    (136917181857232359070005731 / 200000000000000000000000000000) (1095337454857858872694069 / 1600000000000000000000000000) manuscriptNormP5_7Term
    manuscriptNormP5_7_exact_interval hq manuscriptNormP5_7_rounded_endpoints.1 manuscriptNormP5_7_rounded_endpoints.2
  have hw : ((1095337454857858872694069 / 1600000000000000000000000000) - (136917181857232359070005731 / 200000000000000000000000000000) : ℚ) = (8376447 / 100000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_8SubstituteRat_composition_error :
    |manuscriptNormP5_8Term - (manuscriptNormP5_8SubstituteRat : ℝ)| ≤ (((2332135007 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_8SubstituteRat ∈ Set.Icc manuscriptNormP5_8Interval.1 manuscriptNormP5_8Interval.2 := by
    simpa only [manuscriptNormP5_8SubstituteRat, manuscriptNormP5_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_8Interval.1 manuscriptNormP5_8Interval.2 manuscriptNormP5_8SubstituteRat
    (-1695532107765573608087953091 / 1000000000000000000000000000000) (-1695532107765573584766603021 / 1000000000000000000000000000000) manuscriptNormP5_8Term
    manuscriptNormP5_8_exact_interval hq manuscriptNormP5_8_rounded_endpoints.1 manuscriptNormP5_8_rounded_endpoints.2
  have hw : ((-1695532107765573584766603021 / 1000000000000000000000000000000) - (-1695532107765573608087953091 / 1000000000000000000000000000000) : ℚ) = (2332135007 / 100000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP5_9SubstituteRat_composition_error :
    |manuscriptNormP5_9Term - (manuscriptNormP5_9SubstituteRat : ℝ)| ≤ (((96501781 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP5_9SubstituteRat ∈ Set.Icc manuscriptNormP5_9Interval.1 manuscriptNormP5_9Interval.2 := by
    simpa only [manuscriptNormP5_9SubstituteRat, manuscriptNormP5_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP5_9Interval.1 manuscriptNormP5_9Interval.2 manuscriptNormP5_9SubstituteRat
    (-825452530567521026167866743 / 1000000000000000000000000000000) (-412726265283760513035682481 / 500000000000000000000000000000) manuscriptNormP5_9Term
    manuscriptNormP5_9_exact_interval hq manuscriptNormP5_9_rounded_endpoints.1 manuscriptNormP5_9_rounded_endpoints.2
  have hw : ((-412726265283760513035682481 / 500000000000000000000000000000) - (-825452530567521026167866743 / 1000000000000000000000000000000) : ℚ) = (96501781 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow5_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 5 (0, 0)) - (manuscriptNormPSubstituteRow5 : ℝ)| ≤ (((37556040467 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP5_0SubstituteRat_composition_error
  have h1 := manuscriptNormP5_1SubstituteRat_composition_error
  have h2 := manuscriptNormP5_2SubstituteRat_composition_error
  have h3 := manuscriptNormP5_3SubstituteRat_composition_error
  have h4 := manuscriptNormP5_4SubstituteRat_composition_error
  have h5 := manuscriptNormP5_5SubstituteRat_composition_error
  have h6 := manuscriptNormP5_6SubstituteRat_composition_error
  have h7 := manuscriptNormP5_7SubstituteRat_composition_error
  have h8 := manuscriptNormP5_8SubstituteRat_composition_error
  have h9 := manuscriptNormP5_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP5_0Term + (manuscriptNormP5_1Term + (manuscriptNormP5_2Term + (manuscriptNormP5_3Term + (manuscriptNormP5_4Term + (manuscriptNormP5_5Term + (manuscriptNormP5_6Term + (manuscriptNormP5_7Term + (manuscriptNormP5_8Term + (manuscriptNormP5_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow5 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow5
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

def manuscriptNormP5_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP5_0RoundedSubstituteRat_error :
    |(manuscriptNormP5_0SubstituteRat : ℝ) - (manuscriptNormP5_0RoundedSubstituteRat : ℝ)| ≤
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num) (by norm_num)
  have hw : |(((-2875428436063 / 5000000000000000) : ℚ) : ℝ)| + |(((2802770610277 / 1000000000000000) : ℚ) : ℝ)| =
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP5_1RoundedSubstituteRat_error :
    |(manuscriptNormP5_1SubstituteRat : ℝ) - (manuscriptNormP5_1RoundedSubstituteRat : ℝ)| ≤
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799) (by norm_num) (by norm_num)
  have hw : |(((-2637591701359 / 20000000000000000) : ℚ) : ℝ)| + |(((2570943658261 / 4000000000000000) : ℚ) : ℝ)| =
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP5_2RoundedSubstituteRat_error :
    |(manuscriptNormP5_2SubstituteRat : ℝ) - (manuscriptNormP5_2RoundedSubstituteRat : ℝ)| ≤
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((109898540610783 / 40000000000000000) : ℚ) : ℝ)| + |(((437141826370109 / 40000000000000000) : ℚ) : ℝ)| =
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP5_3RoundedSubstituteRat_error :
    |(manuscriptNormP5_3SubstituteRat : ℝ) - (manuscriptNormP5_3RoundedSubstituteRat : ℝ)| ≤
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-273161078429227 / 40000000000000000) : ℚ) : ℝ)| + |(((358543847837271 / 40000000000000000) : ℚ) : ℝ)| =
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP5_4RoundedSubstituteRat_error :
    |(manuscriptNormP5_4SubstituteRat : ℝ) - (manuscriptNormP5_4RoundedSubstituteRat : ℝ)| ≤
      (((18774355590913 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-18774355590913 / 20000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((18774355590913 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP5_5RoundedSubstituteRat_error :
    |(manuscriptNormP5_5SubstituteRat : ℝ) - (manuscriptNormP5_5RoundedSubstituteRat : ℝ)| ≤
      (((24650555122007 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((2157173925639 / 2500000000000000) : ℚ) : ℝ)| + |(((1478632743379 / 4000000000000000) : ℚ) : ℝ)| =
      (((24650555122007 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP5_6RoundedSubstituteRat_error :
    |(manuscriptNormP5_6SubstituteRat : ℝ) - (manuscriptNormP5_6RoundedSubstituteRat : ℝ)| ≤
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num) (by norm_num)
  have hw : |(((-14391556077387 / 10000000000000000) : ℚ) : ℝ)| + |(((1045946527347 / 5000000000000000) : ℚ) : ℝ)| =
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP5_7RoundedSubstituteRat_error :
    |(manuscriptNormP5_7SubstituteRat : ℝ) - (manuscriptNormP5_7RoundedSubstituteRat : ℝ)| ≤
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((6202476756039 / 5000000000000000) : ℚ) : ℝ)| + |(((7590127221861 / 10000000000000000) : ℚ) : ℝ)| =
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP5_8RoundedSubstituteRat_error :
    |(manuscriptNormP5_8SubstituteRat : ℝ) - (manuscriptNormP5_8RoundedSubstituteRat : ℝ)| ≤
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num) (by norm_num)
  have hw : |(((51978482934179 / 40000000000000000) : ℚ) : ℝ)| + |(((23836077867557 / 40000000000000000) : ℚ) : ℝ)| =
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP5_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP5_9RoundedSubstituteRat_error :
    |(manuscriptNormP5_9SubstituteRat : ℝ) - (manuscriptNormP5_9RoundedSubstituteRat : ℝ)| ≤
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((-57165053974051 / 40000000000000000) : ℚ) : ℝ)| + |(((1441492417883 / 40000000000000000) : ℚ) : ℝ)| =
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow5 : ℚ :=
  manuscriptNormP5_0RoundedSubstituteRat +
    manuscriptNormP5_1RoundedSubstituteRat +
    manuscriptNormP5_2RoundedSubstituteRat +
    manuscriptNormP5_3RoundedSubstituteRat +
    manuscriptNormP5_4RoundedSubstituteRat +
    manuscriptNormP5_5RoundedSubstituteRat +
    manuscriptNormP5_6RoundedSubstituteRat +
    manuscriptNormP5_7RoundedSubstituteRat +
    manuscriptNormP5_8RoundedSubstituteRat +
    manuscriptNormP5_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow5_error :
    |(manuscriptNormPSubstituteRow5 : ℝ) - (manuscriptNormPRoundedSubstituteRow5 : ℝ)| ≤
      (((428007303303973 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP5_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP5_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP5_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP5_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP5_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP5_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP5_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP5_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP5_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP5_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow5 manuscriptNormPRoundedSubstituteRow5
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

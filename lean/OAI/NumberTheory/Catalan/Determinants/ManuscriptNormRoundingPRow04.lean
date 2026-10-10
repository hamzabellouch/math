import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup013
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup014
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup015
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup016
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP4_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP4_0SubstituteRat_interval :
    manuscriptNormP4_0SubstituteRat ∈ Set.Icc manuscriptNormP4_0Interval.1 manuscriptNormP4_0Interval.2 := by
  simpa only [manuscriptNormP4_0SubstituteRat, manuscriptNormP4_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num))

private theorem manuscriptNormP4_0SubstituteRat_upper :
    manuscriptNormP4_0SubstituteRat ≤ (-117148695045692465091096139 / 62500000000000000000000000000) :=
  manuscriptNormP4_0SubstituteRat_interval.2.trans manuscriptNormP4_0_rounded_endpoints.2

def manuscriptNormP4_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP4_1SubstituteRat_interval :
    manuscriptNormP4_1SubstituteRat ∈ Set.Icc manuscriptNormP4_1Interval.1 manuscriptNormP4_1Interval.2 := by
  simpa only [manuscriptNormP4_1SubstituteRat, manuscriptNormP4_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num))

private theorem manuscriptNormP4_1SubstituteRat_upper :
    manuscriptNormP4_1SubstituteRat ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) :=
  manuscriptNormP4_1SubstituteRat_interval.2.trans manuscriptNormP4_1_rounded_endpoints.2

def manuscriptNormP4_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP4_2SubstituteRat_interval :
    manuscriptNormP4_2SubstituteRat ∈ Set.Icc manuscriptNormP4_2Interval.1 manuscriptNormP4_2Interval.2 := by
  simpa only [manuscriptNormP4_2SubstituteRat, manuscriptNormP4_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))

private theorem manuscriptNormP4_2SubstituteRat_upper :
    manuscriptNormP4_2SubstituteRat ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) :=
  manuscriptNormP4_2SubstituteRat_interval.2.trans manuscriptNormP4_2_rounded_endpoints.2

def manuscriptNormP4_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP4_3SubstituteRat_interval :
    manuscriptNormP4_3SubstituteRat ∈ Set.Icc manuscriptNormP4_3Interval.1 manuscriptNormP4_3Interval.2 := by
  simpa only [manuscriptNormP4_3SubstituteRat, manuscriptNormP4_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))

private theorem manuscriptNormP4_3SubstituteRat_upper :
    manuscriptNormP4_3SubstituteRat ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) :=
  manuscriptNormP4_3SubstituteRat_interval.2.trans manuscriptNormP4_3_rounded_endpoints.2

def manuscriptNormP4_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP4_4SubstituteRat_interval :
    manuscriptNormP4_4SubstituteRat ∈ Set.Icc manuscriptNormP4_4Interval.1 manuscriptNormP4_4Interval.2 := by
  simpa only [manuscriptNormP4_4SubstituteRat, manuscriptNormP4_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num))

private theorem manuscriptNormP4_4SubstituteRat_upper :
    manuscriptNormP4_4SubstituteRat ≤ (469208388071489204645537183 / 1000000000000000000000000000000) :=
  manuscriptNormP4_4SubstituteRat_interval.2.trans manuscriptNormP4_4_rounded_endpoints.2

def manuscriptNormP4_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP4_5SubstituteRat_interval :
    manuscriptNormP4_5SubstituteRat ∈ Set.Icc manuscriptNormP4_5Interval.1 manuscriptNormP4_5Interval.2 := by
  simpa only [manuscriptNormP4_5SubstituteRat, manuscriptNormP4_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))

private theorem manuscriptNormP4_5SubstituteRat_upper :
    manuscriptNormP4_5SubstituteRat ≤ (1203374562608596014442386537 / 1000000000000000000000000000000) :=
  manuscriptNormP4_5SubstituteRat_interval.2.trans manuscriptNormP4_5_rounded_endpoints.2

def manuscriptNormP4_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP4_6SubstituteRat_interval :
    manuscriptNormP4_6SubstituteRat ∈ Set.Icc manuscriptNormP4_6Interval.1 manuscriptNormP4_6Interval.2 := by
  simpa only [manuscriptNormP4_6SubstituteRat, manuscriptNormP4_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))

private theorem manuscriptNormP4_6SubstituteRat_upper :
    manuscriptNormP4_6SubstituteRat ≤ (1095337454857858872694069 / 1600000000000000000000000000) :=
  manuscriptNormP4_6SubstituteRat_interval.2.trans manuscriptNormP4_6_rounded_endpoints.2

def manuscriptNormP4_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP4_7SubstituteRat_interval :
    manuscriptNormP4_7SubstituteRat ∈ Set.Icc manuscriptNormP4_7Interval.1 manuscriptNormP4_7Interval.2 := by
  simpa only [manuscriptNormP4_7SubstituteRat, manuscriptNormP4_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))

private theorem manuscriptNormP4_7SubstituteRat_upper :
    manuscriptNormP4_7SubstituteRat ≤ (63533058089705813132507881 / 31250000000000000000000000000) :=
  manuscriptNormP4_7SubstituteRat_interval.2.trans manuscriptNormP4_7_rounded_endpoints.2

def manuscriptNormP4_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP4_8SubstituteRat_interval :
    manuscriptNormP4_8SubstituteRat ∈ Set.Icc manuscriptNormP4_8Interval.1 manuscriptNormP4_8Interval.2 := by
  simpa only [manuscriptNormP4_8SubstituteRat, manuscriptNormP4_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))

private theorem manuscriptNormP4_8SubstituteRat_upper :
    manuscriptNormP4_8SubstituteRat ≤ (-412726265283760513035682481 / 500000000000000000000000000000) :=
  manuscriptNormP4_8SubstituteRat_interval.2.trans manuscriptNormP4_8_rounded_endpoints.2

def manuscriptNormP4_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP4_9SubstituteRat_interval :
    manuscriptNormP4_9SubstituteRat ∈ Set.Icc manuscriptNormP4_9Interval.1 manuscriptNormP4_9Interval.2 := by
  simpa only [manuscriptNormP4_9SubstituteRat, manuscriptNormP4_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))

private theorem manuscriptNormP4_9SubstituteRat_upper :
    manuscriptNormP4_9SubstituteRat ≤ (-21194151347069669875047383 / 12500000000000000000000000000) :=
  manuscriptNormP4_9SubstituteRat_interval.2.trans manuscriptNormP4_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow4 : ℚ :=
  manuscriptNormP4_0SubstituteRat +
    manuscriptNormP4_1SubstituteRat +
    manuscriptNormP4_2SubstituteRat +
    manuscriptNormP4_3SubstituteRat +
    manuscriptNormP4_4SubstituteRat +
    manuscriptNormP4_5SubstituteRat +
    manuscriptNormP4_6SubstituteRat +
    manuscriptNormP4_7SubstituteRat +
    manuscriptNormP4_8SubstituteRat +
    manuscriptNormP4_9SubstituteRat

theorem manuscriptNormPSubstituteRow4_upper : manuscriptNormPSubstituteRow4 ≤ (-245704771404397789985869221 / 40000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow4
  linarith only [manuscriptNormP4_0SubstituteRat_upper,
    manuscriptNormP4_1SubstituteRat_upper,
    manuscriptNormP4_2SubstituteRat_upper,
    manuscriptNormP4_3SubstituteRat_upper,
    manuscriptNormP4_4SubstituteRat_upper,
    manuscriptNormP4_5SubstituteRat_upper,
    manuscriptNormP4_6SubstituteRat_upper,
    manuscriptNormP4_7SubstituteRat_upper,
    manuscriptNormP4_8SubstituteRat_upper,
    manuscriptNormP4_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP4_0SubstituteRat_composition_error :
    |manuscriptNormP4_0Term - (manuscriptNormP4_0SubstituteRat : ℝ)| ≤ (((101606546013 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_0SubstituteRat ∈ Set.Icc manuscriptNormP4_0Interval.1 manuscriptNormP4_0Interval.2 := by
    simpa only [manuscriptNormP4_0SubstituteRat, manuscriptNormP4_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_0Interval.1 manuscriptNormP4_0Interval.2 manuscriptNormP4_0SubstituteRat
    (-1874379120731079543064084237 / 1000000000000000000000000000000) (-117148695045692465091096139 / 62500000000000000000000000000) manuscriptNormP4_0Term
    manuscriptNormP4_0_exact_interval hq manuscriptNormP4_0_rounded_endpoints.1 manuscriptNormP4_0_rounded_endpoints.2
  have hw : ((-117148695045692465091096139 / 62500000000000000000000000000) - (-1874379120731079543064084237 / 1000000000000000000000000000000) : ℚ) = (101606546013 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_1SubstituteRat_composition_error :
    |manuscriptNormP4_1Term - (manuscriptNormP4_1SubstituteRat : ℝ)| ≤ (((11650289219 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_1SubstituteRat ∈ Set.Icc manuscriptNormP4_1Interval.1 manuscriptNormP4_1Interval.2 := by
    simpa only [manuscriptNormP4_1SubstituteRat, manuscriptNormP4_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_1Interval.1 manuscriptNormP4_1Interval.2 manuscriptNormP4_1SubstituteRat
    (-465843978124225478021104641 / 1000000000000000000000000000000) (-465843978124225454720526203 / 1000000000000000000000000000000) manuscriptNormP4_1Term
    manuscriptNormP4_1_exact_interval hq manuscriptNormP4_1_rounded_endpoints.1 manuscriptNormP4_1_rounded_endpoints.2
  have hw : ((-465843978124225454720526203 / 1000000000000000000000000000000) - (-465843978124225478021104641 / 1000000000000000000000000000000) : ℚ) = (11650289219 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_2SubstituteRat_composition_error :
    |manuscriptNormP4_2Term - (manuscriptNormP4_2SubstituteRat : ℝ)| ≤ (((230564907 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_2SubstituteRat ∈ Set.Icc manuscriptNormP4_2Interval.1 manuscriptNormP4_2Interval.2 := by
    simpa only [manuscriptNormP4_2SubstituteRat, manuscriptNormP4_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_2Interval.1 manuscriptNormP4_2Interval.2 manuscriptNormP4_2SubstituteRat
    (-127531733280728920730965549 / 40000000000000000000000000000) (-3188293332018223017813008911 / 1000000000000000000000000000000) manuscriptNormP4_2Term
    manuscriptNormP4_2_exact_interval hq manuscriptNormP4_2_rounded_endpoints.1 manuscriptNormP4_2_rounded_endpoints.2
  have hw : ((-3188293332018223017813008911 / 1000000000000000000000000000000) - (-127531733280728920730965549 / 40000000000000000000000000000) : ℚ) = (230564907 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_3SubstituteRat_composition_error :
    |manuscriptNormP4_3Term - (manuscriptNormP4_3SubstituteRat : ℝ)| ≤ (((278283571 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_3SubstituteRat ∈ Set.Icc manuscriptNormP4_3Interval.1 manuscriptNormP4_3Interval.2 := by
    simpa only [manuscriptNormP4_3SubstituteRat, manuscriptNormP4_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_3Interval.1 manuscriptNormP4_3Interval.2 manuscriptNormP4_3SubstituteRat
    (-620836233685038813724759441 / 250000000000000000000000000000) (-1241672467370077627171235311 / 500000000000000000000000000000) manuscriptNormP4_3Term
    manuscriptNormP4_3_exact_interval hq manuscriptNormP4_3_rounded_endpoints.1 manuscriptNormP4_3_rounded_endpoints.2
  have hw : ((-1241672467370077627171235311 / 500000000000000000000000000000) - (-620836233685038813724759441 / 250000000000000000000000000000) : ℚ) = (278283571 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_4SubstituteRat_composition_error :
    |manuscriptNormP4_4Term - (manuscriptNormP4_4SubstituteRat : ℝ)| ≤ (((1456631 / 25000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_4SubstituteRat ∈ Set.Icc manuscriptNormP4_4Interval.1 manuscriptNormP4_4Interval.2 := by
    simpa only [manuscriptNormP4_4SubstituteRat, manuscriptNormP4_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_4Interval.1 manuscriptNormP4_4Interval.2 manuscriptNormP4_4SubstituteRat
    (469208388071489204587271943 / 1000000000000000000000000000000) (469208388071489204645537183 / 1000000000000000000000000000000) manuscriptNormP4_4Term
    manuscriptNormP4_4_exact_interval hq manuscriptNormP4_4_rounded_endpoints.1 manuscriptNormP4_4_rounded_endpoints.2
  have hw : ((469208388071489204645537183 / 1000000000000000000000000000000) - (469208388071489204587271943 / 1000000000000000000000000000000) : ℚ) = (1456631 / 25000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_5SubstituteRat_composition_error :
    |manuscriptNormP4_5Term - (manuscriptNormP4_5SubstituteRat : ℝ)| ≤ (((50709509 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_5SubstituteRat ∈ Set.Icc manuscriptNormP4_5Interval.1 manuscriptNormP4_5Interval.2 := by
    simpa only [manuscriptNormP4_5SubstituteRat, manuscriptNormP4_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_5Interval.1 manuscriptNormP4_5Interval.2 manuscriptNormP4_5SubstituteRat
    (75210910163037250886802437 / 62500000000000000000000000000) (1203374562608596014442386537 / 1000000000000000000000000000000) manuscriptNormP4_5Term
    manuscriptNormP4_5_exact_interval hq manuscriptNormP4_5_rounded_endpoints.1 manuscriptNormP4_5_rounded_endpoints.2
  have hw : ((1203374562608596014442386537 / 1000000000000000000000000000000) - (75210910163037250886802437 / 62500000000000000000000000000) : ℚ) = (50709509 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_6SubstituteRat_composition_error :
    |manuscriptNormP4_6Term - (manuscriptNormP4_6SubstituteRat : ℝ)| ≤ (((8376447 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_6SubstituteRat ∈ Set.Icc manuscriptNormP4_6Interval.1 manuscriptNormP4_6Interval.2 := by
    simpa only [manuscriptNormP4_6SubstituteRat, manuscriptNormP4_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_6Interval.1 manuscriptNormP4_6Interval.2 manuscriptNormP4_6SubstituteRat
    (136917181857232359070005731 / 200000000000000000000000000000) (1095337454857858872694069 / 1600000000000000000000000000) manuscriptNormP4_6Term
    manuscriptNormP4_6_exact_interval hq manuscriptNormP4_6_rounded_endpoints.1 manuscriptNormP4_6_rounded_endpoints.2
  have hw : ((1095337454857858872694069 / 1600000000000000000000000000) - (136917181857232359070005731 / 200000000000000000000000000000) : ℚ) = (8376447 / 100000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_7SubstituteRat_composition_error :
    |manuscriptNormP4_7Term - (manuscriptNormP4_7SubstituteRat : ℝ)| ≤ (((2129692391 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_7SubstituteRat ∈ Set.Icc manuscriptNormP4_7Interval.1 manuscriptNormP4_7Interval.2 := by
    simpa only [manuscriptNormP4_7SubstituteRat, manuscriptNormP4_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_7Interval.1 manuscriptNormP4_7Interval.2 manuscriptNormP4_7SubstituteRat
    (508264464717646502930370657 / 250000000000000000000000000000) (63533058089705813132507881 / 31250000000000000000000000000) manuscriptNormP4_7Term
    manuscriptNormP4_7_exact_interval hq manuscriptNormP4_7_rounded_endpoints.1 manuscriptNormP4_7_rounded_endpoints.2
  have hw : ((63533058089705813132507881 / 31250000000000000000000000000) - (508264464717646502930370657 / 250000000000000000000000000000) : ℚ) = (2129692391 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_8SubstituteRat_composition_error :
    |manuscriptNormP4_8Term - (manuscriptNormP4_8SubstituteRat : ℝ)| ≤ (((96501781 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_8SubstituteRat ∈ Set.Icc manuscriptNormP4_8Interval.1 manuscriptNormP4_8Interval.2 := by
    simpa only [manuscriptNormP4_8SubstituteRat, manuscriptNormP4_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_8Interval.1 manuscriptNormP4_8Interval.2 manuscriptNormP4_8SubstituteRat
    (-825452530567521026167866743 / 1000000000000000000000000000000) (-412726265283760513035682481 / 500000000000000000000000000000) manuscriptNormP4_8Term
    manuscriptNormP4_8_exact_interval hq manuscriptNormP4_8_rounded_endpoints.1 manuscriptNormP4_8_rounded_endpoints.2
  have hw : ((-412726265283760513035682481 / 500000000000000000000000000000) - (-825452530567521026167866743 / 1000000000000000000000000000000) : ℚ) = (96501781 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP4_9SubstituteRat_composition_error :
    |manuscriptNormP4_9Term - (manuscriptNormP4_9SubstituteRat : ℝ)| ≤ (((87749399 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP4_9SubstituteRat ∈ Set.Icc manuscriptNormP4_9Interval.1 manuscriptNormP4_9Interval.2 := by
    simpa only [manuscriptNormP4_9SubstituteRat, manuscriptNormP4_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP4_9Interval.1 manuscriptNormP4_9Interval.2 manuscriptNormP4_9SubstituteRat
    (-339106421553114718088507527 / 200000000000000000000000000000) (-21194151347069669875047383 / 12500000000000000000000000000) manuscriptNormP4_9Term
    manuscriptNormP4_9_exact_interval hq manuscriptNormP4_9_rounded_endpoints.1 manuscriptNormP4_9_rounded_endpoints.2
  have hw : ((-21194151347069669875047383 / 12500000000000000000000000000) - (-339106421553114718088507527 / 200000000000000000000000000000) : ℚ) = (87749399 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow4_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 4 (0, 0)) - (manuscriptNormPSubstituteRow4 : ℝ)| ≤ (((67687208501 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP4_0SubstituteRat_composition_error
  have h1 := manuscriptNormP4_1SubstituteRat_composition_error
  have h2 := manuscriptNormP4_2SubstituteRat_composition_error
  have h3 := manuscriptNormP4_3SubstituteRat_composition_error
  have h4 := manuscriptNormP4_4SubstituteRat_composition_error
  have h5 := manuscriptNormP4_5SubstituteRat_composition_error
  have h6 := manuscriptNormP4_6SubstituteRat_composition_error
  have h7 := manuscriptNormP4_7SubstituteRat_composition_error
  have h8 := manuscriptNormP4_8SubstituteRat_composition_error
  have h9 := manuscriptNormP4_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP4_0Term + (manuscriptNormP4_1Term + (manuscriptNormP4_2Term + (manuscriptNormP4_3Term + (manuscriptNormP4_4Term + (manuscriptNormP4_5Term + (manuscriptNormP4_6Term + (manuscriptNormP4_7Term + (manuscriptNormP4_8Term + (manuscriptNormP4_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow4 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow4
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

def manuscriptNormP4_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP4_0RoundedSubstituteRat_error :
    |(manuscriptNormP4_0SubstituteRat : ℝ) - (manuscriptNormP4_0RoundedSubstituteRat : ℝ)| ≤
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num) (by norm_num)
  have hw : |(((-2875428436063 / 5000000000000000) : ℚ) : ℝ)| + |(((-2802770610277 / 1000000000000000) : ℚ) : ℝ)| =
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP4_1RoundedSubstituteRat_error :
    |(manuscriptNormP4_1SubstituteRat : ℝ) - (manuscriptNormP4_1RoundedSubstituteRat : ℝ)| ≤
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799) (by norm_num) (by norm_num)
  have hw : |(((-2637591701359 / 20000000000000000) : ℚ) : ℝ)| + |(((-2570943658261 / 4000000000000000) : ℚ) : ℝ)| =
      (((1936538749083 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP4_2RoundedSubstituteRat_error :
    |(manuscriptNormP4_2SubstituteRat : ℝ) - (manuscriptNormP4_2RoundedSubstituteRat : ℝ)| ≤
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-273161078429227 / 40000000000000000) : ℚ) : ℝ)| + |(((-358543847837271 / 40000000000000000) : ℚ) : ℝ)| =
      (((315852463133249 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP4_3RoundedSubstituteRat_error :
    |(manuscriptNormP4_3SubstituteRat : ℝ) - (manuscriptNormP4_3RoundedSubstituteRat : ℝ)| ≤
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((109898540610783 / 40000000000000000) : ℚ) : ℝ)| + |(((-437141826370109 / 40000000000000000) : ℚ) : ℝ)| =
      (((136760091745223 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP4_4RoundedSubstituteRat_error :
    |(manuscriptNormP4_4SubstituteRat : ℝ) - (manuscriptNormP4_4RoundedSubstituteRat : ℝ)| ≤
      (((24650555122007 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((2157173925639 / 2500000000000000) : ℚ) : ℝ)| + |(((-1478632743379 / 4000000000000000) : ℚ) : ℝ)| =
      (((24650555122007 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP4_5RoundedSubstituteRat_error :
    |(manuscriptNormP4_5SubstituteRat : ℝ) - (manuscriptNormP4_5RoundedSubstituteRat : ℝ)| ≤
      (((18774355590913 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-18774355590913 / 20000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((18774355590913 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP4_6RoundedSubstituteRat_error :
    |(manuscriptNormP4_6SubstituteRat : ℝ) - (manuscriptNormP4_6RoundedSubstituteRat : ℝ)| ≤
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((6202476756039 / 5000000000000000) : ℚ) : ℝ)| + |(((-7590127221861 / 10000000000000000) : ℚ) : ℝ)| =
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP4_7RoundedSubstituteRat_error :
    |(manuscriptNormP4_7SubstituteRat : ℝ) - (manuscriptNormP4_7RoundedSubstituteRat : ℝ)| ≤
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num) (by norm_num)
  have hw : |(((-14391556077387 / 10000000000000000) : ℚ) : ℝ)| + |(((-1045946527347 / 5000000000000000) : ℚ) : ℝ)| =
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP4_8RoundedSubstituteRat_error :
    |(manuscriptNormP4_8SubstituteRat : ℝ) - (manuscriptNormP4_8RoundedSubstituteRat : ℝ)| ≤
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((-57165053974051 / 40000000000000000) : ℚ) : ℝ)| + |(((-1441492417883 / 40000000000000000) : ℚ) : ℝ)| =
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP4_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP4_9RoundedSubstituteRat_error :
    |(manuscriptNormP4_9SubstituteRat : ℝ) - (manuscriptNormP4_9RoundedSubstituteRat : ℝ)| ≤
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num) (by norm_num)
  have hw : |(((51978482934179 / 40000000000000000) : ℚ) : ℝ)| + |(((-23836077867557 / 40000000000000000) : ℚ) : ℝ)| =
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow4 : ℚ :=
  manuscriptNormP4_0RoundedSubstituteRat +
    manuscriptNormP4_1RoundedSubstituteRat +
    manuscriptNormP4_2RoundedSubstituteRat +
    manuscriptNormP4_3RoundedSubstituteRat +
    manuscriptNormP4_4RoundedSubstituteRat +
    manuscriptNormP4_5RoundedSubstituteRat +
    manuscriptNormP4_6RoundedSubstituteRat +
    manuscriptNormP4_7RoundedSubstituteRat +
    manuscriptNormP4_8RoundedSubstituteRat +
    manuscriptNormP4_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow4_error :
    |(manuscriptNormPSubstituteRow4 : ℝ) - (manuscriptNormPRoundedSubstituteRow4 : ℝ)| ≤
      (((428007303303973 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP4_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP4_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP4_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP4_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP4_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP4_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP4_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP4_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP4_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP4_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow4 manuscriptNormPRoundedSubstituteRow4
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

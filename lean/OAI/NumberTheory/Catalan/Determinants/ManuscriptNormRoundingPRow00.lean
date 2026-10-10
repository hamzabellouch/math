import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup001
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup002
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP0_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-5450417859769 / 625000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP0_0SubstituteRat_interval :
    manuscriptNormP0_0SubstituteRat ∈ Set.Icc manuscriptP00NormLogInterval.1 manuscriptP00NormLogInterval.2 := by
  simpa only [manuscriptNormP0_0SubstituteRat, manuscriptP00NormLogInterval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-5450417859769 / 625000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))

private theorem manuscriptNormP0_0SubstituteRat_upper :
    manuscriptNormP0_0SubstituteRat ≤ (2235864913080284199704102969 / 200000000000000000000000000000) :=
  manuscriptNormP0_0SubstituteRat_interval.2.trans manuscriptP00_rounded_endpoints.2

def manuscriptNormP0_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP0_1SubstituteRat_interval :
    manuscriptNormP0_1SubstituteRat ∈ Set.Icc manuscriptNormP0_1Interval.1 manuscriptNormP0_1Interval.2 := by
  simpa only [manuscriptNormP0_1SubstituteRat, manuscriptNormP0_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num))

private theorem manuscriptNormP0_1SubstituteRat_upper :
    manuscriptNormP0_1SubstituteRat ≤ (3208640661093686384636201629 / 1000000000000000000000000000000) :=
  manuscriptNormP0_1SubstituteRat_interval.2.trans manuscriptNormP0_1_rounded_endpoints.2

def manuscriptNormP0_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP0_2SubstituteRat_interval :
    manuscriptNormP0_2SubstituteRat ∈ Set.Icc manuscriptNormP0_2Interval.1 manuscriptNormP0_2Interval.2 := by
  simpa only [manuscriptNormP0_2SubstituteRat, manuscriptNormP0_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num))

private theorem manuscriptNormP0_2SubstituteRat_upper :
    manuscriptNormP0_2SubstituteRat ≤ (826697653453844082618353217 / 250000000000000000000000000000) :=
  manuscriptNormP0_2SubstituteRat_interval.2.trans manuscriptNormP0_2_rounded_endpoints.2

def manuscriptNormP0_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319)

private theorem manuscriptNormP0_3SubstituteRat_interval :
    manuscriptNormP0_3SubstituteRat ∈ Set.Icc manuscriptNormP0_3Interval.1 manuscriptNormP0_3Interval.2 := by
  simpa only [manuscriptNormP0_3SubstituteRat, manuscriptNormP0_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319) (by norm_num))

private theorem manuscriptNormP0_3SubstituteRat_upper :
    manuscriptNormP0_3SubstituteRat ≤ (826697653453844082618353217 / 250000000000000000000000000000) :=
  manuscriptNormP0_3SubstituteRat_interval.2.trans manuscriptNormP0_3_rounded_endpoints.2

def manuscriptNormP0_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP0_4SubstituteRat_interval :
    manuscriptNormP0_4SubstituteRat ∈ Set.Icc manuscriptNormP0_4Interval.1 manuscriptNormP0_4Interval.2 := by
  simpa only [manuscriptNormP0_4SubstituteRat, manuscriptNormP0_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num))

private theorem manuscriptNormP0_4SubstituteRat_upper :
    manuscriptNormP0_4SubstituteRat ≤ (-117148695045692465091096139 / 62500000000000000000000000000) :=
  manuscriptNormP0_4SubstituteRat_interval.2.trans manuscriptNormP0_4_rounded_endpoints.2

def manuscriptNormP0_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP0_5SubstituteRat_interval :
    manuscriptNormP0_5SubstituteRat ∈ Set.Icc manuscriptNormP0_5Interval.1 manuscriptNormP0_5Interval.2 := by
  simpa only [manuscriptNormP0_5SubstituteRat, manuscriptNormP0_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num))

private theorem manuscriptNormP0_5SubstituteRat_upper :
    manuscriptNormP0_5SubstituteRat ≤ (-117148695045692465091096139 / 62500000000000000000000000000) :=
  manuscriptNormP0_5SubstituteRat_interval.2.trans manuscriptNormP0_5_rounded_endpoints.2

def manuscriptNormP0_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP0_6SubstituteRat_interval :
    manuscriptNormP0_6SubstituteRat ∈ Set.Icc manuscriptNormP0_6Interval.1 manuscriptNormP0_6Interval.2 := by
  simpa only [manuscriptNormP0_6SubstituteRat, manuscriptNormP0_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num))

private theorem manuscriptNormP0_6SubstituteRat_upper :
    manuscriptNormP0_6SubstituteRat ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) :=
  manuscriptNormP0_6SubstituteRat_interval.2.trans manuscriptNormP0_6_rounded_endpoints.2

def manuscriptNormP0_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519)

private theorem manuscriptNormP0_7SubstituteRat_interval :
    manuscriptNormP0_7SubstituteRat ∈ Set.Icc manuscriptNormP0_7Interval.1 manuscriptNormP0_7Interval.2 := by
  simpa only [manuscriptNormP0_7SubstituteRat, manuscriptNormP0_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519) (by norm_num))

private theorem manuscriptNormP0_7SubstituteRat_upper :
    manuscriptNormP0_7SubstituteRat ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) :=
  manuscriptNormP0_7SubstituteRat_interval.2.trans manuscriptNormP0_7_rounded_endpoints.2

def manuscriptNormP0_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP0_8SubstituteRat_interval :
    manuscriptNormP0_8SubstituteRat ∈ Set.Icc manuscriptNormP0_8Interval.1 manuscriptNormP0_8Interval.2 := by
  simpa only [manuscriptNormP0_8SubstituteRat, manuscriptNormP0_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num))

private theorem manuscriptNormP0_8SubstituteRat_upper :
    manuscriptNormP0_8SubstituteRat ≤ (476374564998450126700803411 / 200000000000000000000000000000) :=
  manuscriptNormP0_8SubstituteRat_interval.2.trans manuscriptNormP0_8_rounded_endpoints.2

def manuscriptNormP0_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301)

private theorem manuscriptNormP0_9SubstituteRat_interval :
    manuscriptNormP0_9SubstituteRat ∈ Set.Icc manuscriptNormP0_9Interval.1 manuscriptNormP0_9Interval.2 := by
  simpa only [manuscriptNormP0_9SubstituteRat, manuscriptNormP0_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301) (by norm_num))

private theorem manuscriptNormP0_9SubstituteRat_upper :
    manuscriptNormP0_9SubstituteRat ≤ (476374564998450126700803411 / 200000000000000000000000000000) :=
  manuscriptNormP0_9SubstituteRat_interval.2.trans manuscriptNormP0_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow0 : ℚ :=
  manuscriptNormP0_0SubstituteRat +
    manuscriptNormP0_1SubstituteRat +
    manuscriptNormP0_2SubstituteRat +
    manuscriptNormP0_3SubstituteRat +
    manuscriptNormP0_4SubstituteRat +
    manuscriptNormP0_5SubstituteRat +
    manuscriptNormP0_6SubstituteRat +
    manuscriptNormP0_7SubstituteRat +
    manuscriptNormP0_8SubstituteRat +
    manuscriptNormP0_9SubstituteRat

theorem manuscriptNormPSubstituteRow0_upper : manuscriptNormPSubstituteRow0 ≤ (778974678889387440646188819 / 50000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow0
  linarith only [manuscriptNormP0_0SubstituteRat_upper,
    manuscriptNormP0_1SubstituteRat_upper,
    manuscriptNormP0_2SubstituteRat_upper,
    manuscriptNormP0_3SubstituteRat_upper,
    manuscriptNormP0_4SubstituteRat_upper,
    manuscriptNormP0_5SubstituteRat_upper,
    manuscriptNormP0_6SubstituteRat_upper,
    manuscriptNormP0_7SubstituteRat_upper,
    manuscriptNormP0_8SubstituteRat_upper,
    manuscriptNormP0_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP0_0SubstituteRat_composition_error :
    |manuscriptP00NormLogTerm - (manuscriptNormP0_0SubstituteRat : ℝ)| ≤ (((471090279 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_0SubstituteRat ∈ Set.Icc manuscriptP00NormLogInterval.1 manuscriptP00NormLogInterval.2 := by
    simpa only [manuscriptNormP0_0SubstituteRat, manuscriptP00NormLogInterval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-5450417859769 / 625000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptP00NormLogInterval.1 manuscriptP00NormLogInterval.2 manuscriptNormP0_0SubstituteRat
    (223586491308028419923301269 / 20000000000000000000000000000) (2235864913080284199704102969 / 200000000000000000000000000000) manuscriptP00NormLogTerm
    manuscriptP00_exact_interval hq manuscriptP00_rounded_endpoints.1 manuscriptP00_rounded_endpoints.2
  have hw : ((2235864913080284199704102969 / 200000000000000000000000000000) - (223586491308028419923301269 / 20000000000000000000000000000) : ℚ) = (471090279 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_1SubstituteRat_composition_error :
    |manuscriptNormP0_1Term - (manuscriptNormP0_1SubstituteRat : ℝ)| ≤ (((168798733 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_1SubstituteRat ∈ Set.Icc manuscriptNormP0_1Interval.1 manuscriptNormP0_1Interval.2 := by
    simpa only [manuscriptNormP0_1SubstituteRat, manuscriptNormP0_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_1Interval.1 manuscriptNormP0_1Interval.2 manuscriptNormP0_1SubstituteRat
    (3208640661093686383961006697 / 1000000000000000000000000000000) (3208640661093686384636201629 / 1000000000000000000000000000000) manuscriptNormP0_1Term
    manuscriptNormP0_1_exact_interval hq manuscriptNormP0_1_rounded_endpoints.1 manuscriptNormP0_1_rounded_endpoints.2
  have hw : ((3208640661093686384636201629 / 1000000000000000000000000000000) - (3208640661093686383961006697 / 1000000000000000000000000000000) : ℚ) = (168798733 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_2SubstituteRat_composition_error :
    |manuscriptNormP0_2Term - (manuscriptNormP0_2SubstituteRat : ℝ)| ≤ (((540098219653 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_2SubstituteRat ∈ Set.Icc manuscriptNormP0_2Interval.1 manuscriptNormP0_2Interval.2 := by
    simpa only [manuscriptNormP0_2SubstituteRat, manuscriptNormP0_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_2Interval.1 manuscriptNormP0_2Interval.2 manuscriptNormP0_2SubstituteRat
    (661358122763075158075038643 / 200000000000000000000000000000) (826697653453844082618353217 / 250000000000000000000000000000) manuscriptNormP0_2Term
    manuscriptNormP0_2_exact_interval hq manuscriptNormP0_2_rounded_endpoints.1 manuscriptNormP0_2_rounded_endpoints.2
  have hw : ((826697653453844082618353217 / 250000000000000000000000000000) - (661358122763075158075038643 / 200000000000000000000000000000) : ℚ) = (540098219653 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_3SubstituteRat_composition_error :
    |manuscriptNormP0_3Term - (manuscriptNormP0_3SubstituteRat : ℝ)| ≤ (((540098219653 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_3SubstituteRat ∈ Set.Icc manuscriptNormP0_3Interval.1 manuscriptNormP0_3Interval.2 := by
    simpa only [manuscriptNormP0_3SubstituteRat, manuscriptNormP0_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_3Interval.1 manuscriptNormP0_3Interval.2 manuscriptNormP0_3SubstituteRat
    (661358122763075158075038643 / 200000000000000000000000000000) (826697653453844082618353217 / 250000000000000000000000000000) manuscriptNormP0_3Term
    manuscriptNormP0_3_exact_interval hq manuscriptNormP0_3_rounded_endpoints.1 manuscriptNormP0_3_rounded_endpoints.2
  have hw : ((826697653453844082618353217 / 250000000000000000000000000000) - (661358122763075158075038643 / 200000000000000000000000000000) : ℚ) = (540098219653 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_4SubstituteRat_composition_error :
    |manuscriptNormP0_4Term - (manuscriptNormP0_4SubstituteRat : ℝ)| ≤ (((101606546013 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_4SubstituteRat ∈ Set.Icc manuscriptNormP0_4Interval.1 manuscriptNormP0_4Interval.2 := by
    simpa only [manuscriptNormP0_4SubstituteRat, manuscriptNormP0_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_4Interval.1 manuscriptNormP0_4Interval.2 manuscriptNormP0_4SubstituteRat
    (-1874379120731079543064084237 / 1000000000000000000000000000000) (-117148695045692465091096139 / 62500000000000000000000000000) manuscriptNormP0_4Term
    manuscriptNormP0_4_exact_interval hq manuscriptNormP0_4_rounded_endpoints.1 manuscriptNormP0_4_rounded_endpoints.2
  have hw : ((-117148695045692465091096139 / 62500000000000000000000000000) - (-1874379120731079543064084237 / 1000000000000000000000000000000) : ℚ) = (101606546013 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_5SubstituteRat_composition_error :
    |manuscriptNormP0_5Term - (manuscriptNormP0_5SubstituteRat : ℝ)| ≤ (((101606546013 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_5SubstituteRat ∈ Set.Icc manuscriptNormP0_5Interval.1 manuscriptNormP0_5Interval.2 := by
    simpa only [manuscriptNormP0_5SubstituteRat, manuscriptNormP0_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_5Interval.1 manuscriptNormP0_5Interval.2 manuscriptNormP0_5SubstituteRat
    (-1874379120731079543064084237 / 1000000000000000000000000000000) (-117148695045692465091096139 / 62500000000000000000000000000) manuscriptNormP0_5Term
    manuscriptNormP0_5_exact_interval hq manuscriptNormP0_5_rounded_endpoints.1 manuscriptNormP0_5_rounded_endpoints.2
  have hw : ((-117148695045692465091096139 / 62500000000000000000000000000) - (-1874379120731079543064084237 / 1000000000000000000000000000000) : ℚ) = (101606546013 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_6SubstituteRat_composition_error :
    |manuscriptNormP0_6Term - (manuscriptNormP0_6SubstituteRat : ℝ)| ≤ (((75563940457 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_6SubstituteRat ∈ Set.Icc manuscriptNormP0_6Interval.1 manuscriptNormP0_6Interval.2 := by
    simpa only [manuscriptNormP0_6SubstituteRat, manuscriptNormP0_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_6Interval.1 manuscriptNormP0_6Interval.2 manuscriptNormP0_6SubstituteRat
    (-160926007121511347938212133 / 50000000000000000000000000000) (-1609260071215113403818180873 / 500000000000000000000000000000) manuscriptNormP0_6Term
    manuscriptNormP0_6_exact_interval hq manuscriptNormP0_6_rounded_endpoints.1 manuscriptNormP0_6_rounded_endpoints.2
  have hw : ((-1609260071215113403818180873 / 500000000000000000000000000000) - (-160926007121511347938212133 / 50000000000000000000000000000) : ℚ) = (75563940457 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_7SubstituteRat_composition_error :
    |manuscriptNormP0_7Term - (manuscriptNormP0_7SubstituteRat : ℝ)| ≤ (((75563940457 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_7SubstituteRat ∈ Set.Icc manuscriptNormP0_7Interval.1 manuscriptNormP0_7Interval.2 := by
    simpa only [manuscriptNormP0_7SubstituteRat, manuscriptNormP0_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_7Interval.1 manuscriptNormP0_7Interval.2 manuscriptNormP0_7SubstituteRat
    (-160926007121511347938212133 / 50000000000000000000000000000) (-1609260071215113403818180873 / 500000000000000000000000000000) manuscriptNormP0_7Term
    manuscriptNormP0_7_exact_interval hq manuscriptNormP0_7_rounded_endpoints.1 manuscriptNormP0_7_rounded_endpoints.2
  have hw : ((-1609260071215113403818180873 / 500000000000000000000000000000) - (-160926007121511347938212133 / 50000000000000000000000000000) : ℚ) = (75563940457 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_8SubstituteRat_composition_error :
    |manuscriptNormP0_8Term - (manuscriptNormP0_8SubstituteRat : ℝ)| ≤ (((153887961761 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_8SubstituteRat ∈ Set.Icc manuscriptNormP0_8Interval.1 manuscriptNormP0_8Interval.2 := by
    simpa only [manuscriptNormP0_8SubstituteRat, manuscriptNormP0_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_8Interval.1 manuscriptNormP0_8Interval.2 manuscriptNormP0_8SubstituteRat
    (1190936412496125239808027647 / 500000000000000000000000000000) (476374564998450126700803411 / 200000000000000000000000000000) manuscriptNormP0_8Term
    manuscriptNormP0_8_exact_interval hq manuscriptNormP0_8_rounded_endpoints.1 manuscriptNormP0_8_rounded_endpoints.2
  have hw : ((476374564998450126700803411 / 200000000000000000000000000000) - (1190936412496125239808027647 / 500000000000000000000000000000) : ℚ) = (153887961761 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP0_9SubstituteRat_composition_error :
    |manuscriptNormP0_9Term - (manuscriptNormP0_9SubstituteRat : ℝ)| ≤ (((153887961761 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP0_9SubstituteRat ∈ Set.Icc manuscriptNormP0_9Interval.1 manuscriptNormP0_9Interval.2 := by
    simpa only [manuscriptNormP0_9SubstituteRat, manuscriptNormP0_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP0_9Interval.1 manuscriptNormP0_9Interval.2 manuscriptNormP0_9SubstituteRat
    (1190936412496125239808027647 / 500000000000000000000000000000) (476374564998450126700803411 / 200000000000000000000000000000) manuscriptNormP0_9Term
    manuscriptNormP0_9_exact_interval hq manuscriptNormP0_9_rounded_endpoints.1 manuscriptNormP0_9_rounded_endpoints.2
  have hw : ((476374564998450126700803411 / 200000000000000000000000000000) - (1190936412496125239808027647 / 500000000000000000000000000000) : ℚ) = (153887961761 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow0_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 0 (0, 0)) - (manuscriptNormPSubstituteRow0 : ℝ)| ≤ (((1896471863009 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP0_0SubstituteRat_composition_error
  have h1 := manuscriptNormP0_1SubstituteRat_composition_error
  have h2 := manuscriptNormP0_2SubstituteRat_composition_error
  have h3 := manuscriptNormP0_3SubstituteRat_composition_error
  have h4 := manuscriptNormP0_4SubstituteRat_composition_error
  have h5 := manuscriptNormP0_5SubstituteRat_composition_error
  have h6 := manuscriptNormP0_6SubstituteRat_composition_error
  have h7 := manuscriptNormP0_7SubstituteRat_composition_error
  have h8 := manuscriptNormP0_8SubstituteRat_composition_error
  have h9 := manuscriptNormP0_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptP00NormLogTerm + (manuscriptNormP0_1Term + (manuscriptNormP0_2Term + (manuscriptNormP0_3Term + (manuscriptNormP0_4Term + (manuscriptNormP0_5Term + (manuscriptNormP0_6Term + (manuscriptNormP0_7Term + (manuscriptNormP0_8Term + (manuscriptNormP0_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow0 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow0
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

def manuscriptNormP0_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-5450417859769 / 625000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP0_0RoundedSubstituteRat_error :
    |(manuscriptNormP0_0SubstituteRat : ℝ) - (manuscriptNormP0_0RoundedSubstituteRat : ℝ)| ≤
      (((5450417859769 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-5450417859769 / 625000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-5450417859769 / 625000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((5450417859769 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP0_1RoundedSubstituteRat_error :
    |(manuscriptNormP0_1SubstituteRat : ℝ) - (manuscriptNormP0_1RoundedSubstituteRat : ℝ)| ≤
      (((4999594751017 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-4999594751017 / 2500000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((4999594751017 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP0_2RoundedSubstituteRat_error :
    |(manuscriptNormP0_2SubstituteRat : ℝ) - (manuscriptNormP0_2RoundedSubstituteRat : ℝ)| ≤
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319) (by norm_num) (by norm_num)
  have hw : |(((-77366649157093 / 2500000000000000) : ℚ) : ℝ)| + |(((74491825385797 / 5000000000000000) : ℚ) : ℝ)| =
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319)

private theorem manuscriptNormP0_3RoundedSubstituteRat_error :
    |(manuscriptNormP0_3SubstituteRat : ℝ) - (manuscriptNormP0_3RoundedSubstituteRat : ℝ)| ≤
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319) (by norm_num) (by norm_num)
  have hw : |(((-77366649157093 / 2500000000000000) : ℚ) : ℝ)| + |(((-74491825385797 / 5000000000000000) : ℚ) : ℝ)| =
      (((229225123699983 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP0_4RoundedSubstituteRat_error :
    |(manuscriptNormP0_4SubstituteRat : ℝ) - (manuscriptNormP0_4RoundedSubstituteRat : ℝ)| ≤
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689) (by norm_num) (by norm_num)
  have hw : |(((-2875428436063 / 5000000000000000) : ℚ) : ℝ)| + |(((-2802770610277 / 1000000000000000) : ℚ) : ℝ)| =
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP0_5RoundedSubstituteRat_error :
    |(manuscriptNormP0_5SubstituteRat : ℝ) - (manuscriptNormP0_5RoundedSubstituteRat : ℝ)| ≤
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689) (by norm_num) (by norm_num)
  have hw : |(((-2875428436063 / 5000000000000000) : ℚ) : ℝ)| + |(((2802770610277 / 1000000000000000) : ℚ) : ℝ)| =
      (((2111160185931 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP0_6RoundedSubstituteRat_error :
    |(manuscriptNormP0_6SubstituteRat : ℝ) - (manuscriptNormP0_6RoundedSubstituteRat : ℝ)| ≤
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num) (by norm_num)
  have hw : |(((-3765635049867 / 2500000000000000) : ℚ) : ℝ)| + |(((-10421985581721 / 2500000000000000) : ℚ) : ℝ)| =
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519)

private theorem manuscriptNormP0_7RoundedSubstituteRat_error :
    |(manuscriptNormP0_7SubstituteRat : ℝ) - (manuscriptNormP0_7RoundedSubstituteRat : ℝ)| ≤
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519) (by norm_num) (by norm_num)
  have hw : |(((-3765635049867 / 2500000000000000) : ℚ) : ℝ)| + |(((10421985581721 / 2500000000000000) : ℚ) : ℝ)| =
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP0_8RoundedSubstituteRat_error :
    |(manuscriptNormP0_8SubstituteRat : ℝ) - (manuscriptNormP0_8RoundedSubstituteRat : ℝ)| ≤
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num) (by norm_num)
  have hw : |(((-76806433087 / 78125000000000) : ℚ) : ℝ)| + |(((21224636816931 / 5000000000000000) : ℚ) : ℝ)| =
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP0_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301)

private theorem manuscriptNormP0_9RoundedSubstituteRat_error :
    |(manuscriptNormP0_9SubstituteRat : ℝ) - (manuscriptNormP0_9RoundedSubstituteRat : ℝ)| ≤
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301) (by norm_num) (by norm_num)
  have hw : |(((-76806433087 / 78125000000000) : ℚ) : ℝ)| + |(((-21224636816931 / 5000000000000000) : ℚ) : ℝ)| =
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow0 : ℚ :=
  manuscriptNormP0_0RoundedSubstituteRat +
    manuscriptNormP0_1RoundedSubstituteRat +
    manuscriptNormP0_2RoundedSubstituteRat +
    manuscriptNormP0_3RoundedSubstituteRat +
    manuscriptNormP0_4RoundedSubstituteRat +
    manuscriptNormP0_5RoundedSubstituteRat +
    manuscriptNormP0_6RoundedSubstituteRat +
    manuscriptNormP0_7RoundedSubstituteRat +
    manuscriptNormP0_8RoundedSubstituteRat +
    manuscriptNormP0_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow0_error :
    |(manuscriptNormPSubstituteRow0 : ℝ) - (manuscriptNormPRoundedSubstituteRow0 : ℝ)| ≤
      (((327431161175199 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP0_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP0_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP0_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP0_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP0_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP0_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP0_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP0_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP0_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP0_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow0 manuscriptNormPRoundedSubstituteRow0
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

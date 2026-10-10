import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup017
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup018
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup019
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup020
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup021
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV4_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV4_0SubstituteRat_interval :
    manuscriptNormV4_0SubstituteRat ∈ Set.Icc manuscriptNormV4_0Interval.1 manuscriptNormV4_0Interval.2 := by
  simpa only [manuscriptNormV4_0SubstituteRat, manuscriptNormV4_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num))

private theorem manuscriptNormV4_0SubstituteRat_upper :
    manuscriptNormV4_0SubstituteRat ≤ (-2050703264279718561958939307 / 200000000000000000000000000000) :=
  manuscriptNormV4_0SubstituteRat_interval.2.trans manuscriptNormV4_0_rounded_endpoints.2

def manuscriptNormV4_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV4_1SubstituteRat_interval :
    manuscriptNormV4_1SubstituteRat ∈ Set.Icc manuscriptNormV4_1Interval.1 manuscriptNormV4_1Interval.2 := by
  simpa only [manuscriptNormV4_1SubstituteRat, manuscriptNormV4_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num))

private theorem manuscriptNormV4_1SubstituteRat_upper :
    manuscriptNormV4_1SubstituteRat ≤ (-1719892378039867589719800831 / 500000000000000000000000000000) :=
  manuscriptNormV4_1SubstituteRat_interval.2.trans manuscriptNormV4_1_rounded_endpoints.2

def manuscriptNormV4_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV4_2SubstituteRat_interval :
    manuscriptNormV4_2SubstituteRat ∈ Set.Icc manuscriptNormV4_2Interval.1 manuscriptNormV4_2Interval.2 := by
  simpa only [manuscriptNormV4_2SubstituteRat, manuscriptNormV4_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV4_2SubstituteRat_upper :
    manuscriptNormV4_2SubstituteRat ≤ (2971062291974073186134220553 / 500000000000000000000000000000) :=
  manuscriptNormV4_2SubstituteRat_interval.2.trans manuscriptNormV4_2_rounded_endpoints.2

def manuscriptNormV4_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV4_3SubstituteRat_interval :
    manuscriptNormV4_3SubstituteRat ∈ Set.Icc manuscriptNormV4_3Interval.1 manuscriptNormV4_3Interval.2 := by
  simpa only [manuscriptNormV4_3SubstituteRat, manuscriptNormV4_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num))

private theorem manuscriptNormV4_3SubstituteRat_upper :
    manuscriptNormV4_3SubstituteRat ≤ (-97792568524825520647620519 / 6250000000000000000000000000) :=
  manuscriptNormV4_3SubstituteRat_interval.2.trans manuscriptNormV4_3_rounded_endpoints.2

def manuscriptNormV4_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV4_4SubstituteRat_interval :
    manuscriptNormV4_4SubstituteRat ∈ Set.Icc manuscriptNormV4_4Interval.1 manuscriptNormV4_4Interval.2 := by
  simpa only [manuscriptNormV4_4SubstituteRat, manuscriptNormV4_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormV4_4SubstituteRat_upper :
    manuscriptNormV4_4SubstituteRat ≤ (46569338167827476758832787763 / 1000000000000000000000000000000) :=
  manuscriptNormV4_4SubstituteRat_interval.2.trans manuscriptNormV4_4_rounded_endpoints.2

def manuscriptNormV4_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV4_5SubstituteRat_interval :
    manuscriptNormV4_5SubstituteRat ∈ Set.Icc manuscriptNormV4_5Interval.1 manuscriptNormV4_5Interval.2 := by
  simpa only [manuscriptNormV4_5SubstituteRat, manuscriptNormV4_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num))

private theorem manuscriptNormV4_5SubstituteRat_upper :
    manuscriptNormV4_5SubstituteRat ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) :=
  manuscriptNormV4_5SubstituteRat_interval.2.trans manuscriptNormV4_5_rounded_endpoints.2

def manuscriptNormV4_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047)

private theorem manuscriptNormV4_6SubstituteRat_interval :
    manuscriptNormV4_6SubstituteRat ∈ Set.Icc manuscriptNormV4_6Interval.1 manuscriptNormV4_6Interval.2 := by
  simpa only [manuscriptNormV4_6SubstituteRat, manuscriptNormV4_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047) (by norm_num))

private theorem manuscriptNormV4_6SubstituteRat_upper :
    manuscriptNormV4_6SubstituteRat ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) :=
  manuscriptNormV4_6SubstituteRat_interval.2.trans manuscriptNormV4_6_rounded_endpoints.2

def manuscriptNormV4_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357)

private theorem manuscriptNormV4_7SubstituteRat_interval :
    manuscriptNormV4_7SubstituteRat ∈ Set.Icc manuscriptNormV4_7Interval.1 manuscriptNormV4_7Interval.2 := by
  simpa only [manuscriptNormV4_7SubstituteRat, manuscriptNormV4_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357) (by norm_num))

private theorem manuscriptNormV4_7SubstituteRat_upper :
    manuscriptNormV4_7SubstituteRat ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) :=
  manuscriptNormV4_7SubstituteRat_interval.2.trans manuscriptNormV4_7_rounded_endpoints.2

def manuscriptNormV4_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV4_8SubstituteRat_interval :
    manuscriptNormV4_8SubstituteRat ∈ Set.Icc manuscriptNormV4_8Interval.1 manuscriptNormV4_8Interval.2 := by
  simpa only [manuscriptNormV4_8SubstituteRat, manuscriptNormV4_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num))

private theorem manuscriptNormV4_8SubstituteRat_upper :
    manuscriptNormV4_8SubstituteRat ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) :=
  manuscriptNormV4_8SubstituteRat_interval.2.trans manuscriptNormV4_8_rounded_endpoints.2

def manuscriptNormV4_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493)

private theorem manuscriptNormV4_9SubstituteRat_interval :
    manuscriptNormV4_9SubstituteRat ∈ Set.Icc manuscriptNormV4_9Interval.1 manuscriptNormV4_9Interval.2 := by
  simpa only [manuscriptNormV4_9SubstituteRat, manuscriptNormV4_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493) (by norm_num))

private theorem manuscriptNormV4_9SubstituteRat_upper :
    manuscriptNormV4_9SubstituteRat ≤ (3225193972171665872211150519 / 500000000000000000000000000000) :=
  manuscriptNormV4_9SubstituteRat_interval.2.trans manuscriptNormV4_9_rounded_endpoints.2

def manuscriptNormV4_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV4_10SubstituteRat_interval :
    manuscriptNormV4_10SubstituteRat ∈ Set.Icc manuscriptNormV4_10Interval.1 manuscriptNormV4_10Interval.2 := by
  simpa only [manuscriptNormV4_10SubstituteRat, manuscriptNormV4_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num))

private theorem manuscriptNormV4_10SubstituteRat_upper :
    manuscriptNormV4_10SubstituteRat ≤ (3225193972171665872211150519 / 500000000000000000000000000000) :=
  manuscriptNormV4_10SubstituteRat_interval.2.trans manuscriptNormV4_10_rounded_endpoints.2

def manuscriptNormV4_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV4_11SubstituteRat_interval :
    manuscriptNormV4_11SubstituteRat ∈ Set.Icc manuscriptNormV4_11Interval.1 manuscriptNormV4_11Interval.2 := by
  simpa only [manuscriptNormV4_11SubstituteRat, manuscriptNormV4_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num))

private theorem manuscriptNormV4_11SubstituteRat_upper :
    manuscriptNormV4_11SubstituteRat ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) :=
  manuscriptNormV4_11SubstituteRat_interval.2.trans manuscriptNormV4_11_rounded_endpoints.2

def manuscriptNormV4_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV4_12SubstituteRat_interval :
    manuscriptNormV4_12SubstituteRat ∈ Set.Icc manuscriptNormV4_12Interval.1 manuscriptNormV4_12Interval.2 := by
  simpa only [manuscriptNormV4_12SubstituteRat, manuscriptNormV4_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num))

private theorem manuscriptNormV4_12SubstituteRat_upper :
    manuscriptNormV4_12SubstituteRat ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) :=
  manuscriptNormV4_12SubstituteRat_interval.2.trans manuscriptNormV4_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow4 : ℚ :=
  manuscriptNormV4_0SubstituteRat +
    manuscriptNormV4_1SubstituteRat +
    manuscriptNormV4_2SubstituteRat +
    manuscriptNormV4_3SubstituteRat +
    manuscriptNormV4_4SubstituteRat +
    manuscriptNormV4_5SubstituteRat +
    manuscriptNormV4_6SubstituteRat +
    manuscriptNormV4_7SubstituteRat +
    manuscriptNormV4_8SubstituteRat +
    manuscriptNormV4_9SubstituteRat +
    manuscriptNormV4_10SubstituteRat +
    manuscriptNormV4_11SubstituteRat +
    manuscriptNormV4_12SubstituteRat

theorem manuscriptNormVSubstituteRow4_upper : manuscriptNormVSubstituteRow4 ≤ (-17788016786043582944131371579 / 500000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow4
  linarith only [manuscriptNormV4_0SubstituteRat_upper,
    manuscriptNormV4_1SubstituteRat_upper,
    manuscriptNormV4_2SubstituteRat_upper,
    manuscriptNormV4_3SubstituteRat_upper,
    manuscriptNormV4_4SubstituteRat_upper,
    manuscriptNormV4_5SubstituteRat_upper,
    manuscriptNormV4_6SubstituteRat_upper,
    manuscriptNormV4_7SubstituteRat_upper,
    manuscriptNormV4_8SubstituteRat_upper,
    manuscriptNormV4_9SubstituteRat_upper,
    manuscriptNormV4_10SubstituteRat_upper,
    manuscriptNormV4_11SubstituteRat_upper,
    manuscriptNormV4_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV4_0SubstituteRat_composition_error :
    |manuscriptNormV4_0Term - (manuscriptNormV4_0SubstituteRat : ℝ)| ≤ (((596201549 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_0SubstituteRat ∈ Set.Icc manuscriptNormV4_0Interval.1 manuscriptNormV4_0Interval.2 := by
    simpa only [manuscriptNormV4_0SubstituteRat, manuscriptNormV4_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_0Interval.1 manuscriptNormV4_0Interval.2 manuscriptNormV4_0SubstituteRat
    (-10253516321398592810987099633 / 1000000000000000000000000000000) (-2050703264279718561958939307 / 200000000000000000000000000000) manuscriptNormV4_0Term
    manuscriptNormV4_0_exact_interval hq manuscriptNormV4_0_rounded_endpoints.1 manuscriptNormV4_0_rounded_endpoints.2
  have hw : ((-2050703264279718561958939307 / 200000000000000000000000000000) - (-10253516321398592810987099633 / 1000000000000000000000000000000) : ℚ) = (596201549 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_1SubstituteRat_composition_error :
    |manuscriptNormV4_1Term - (manuscriptNormV4_1SubstituteRat : ℝ)| ≤ (((45999499 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_1SubstituteRat ∈ Set.Icc manuscriptNormV4_1Interval.1 manuscriptNormV4_1Interval.2 := by
    simpa only [manuscriptNormV4_1SubstituteRat, manuscriptNormV4_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_1Interval.1 manuscriptNormV4_1Interval.2 manuscriptNormV4_1SubstituteRat
    (-1719892378039867589903798827 / 500000000000000000000000000000) (-1719892378039867589719800831 / 500000000000000000000000000000) manuscriptNormV4_1Term
    manuscriptNormV4_1_exact_interval hq manuscriptNormV4_1_rounded_endpoints.1 manuscriptNormV4_1_rounded_endpoints.2
  have hw : ((-1719892378039867589719800831 / 500000000000000000000000000000) - (-1719892378039867589903798827 / 500000000000000000000000000000) : ℚ) = (45999499 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_2SubstituteRat_composition_error :
    |manuscriptNormV4_2Term - (manuscriptNormV4_2SubstituteRat : ℝ)| ≤ (((1198142749 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_2SubstituteRat ∈ Set.Icc manuscriptNormV4_2Interval.1 manuscriptNormV4_2Interval.2 := by
    simpa only [manuscriptNormV4_2SubstituteRat, manuscriptNormV4_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_2Interval.1 manuscriptNormV4_2Interval.2 manuscriptNormV4_2SubstituteRat
    (5942124583948146371070298357 / 1000000000000000000000000000000) (2971062291974073186134220553 / 500000000000000000000000000000) manuscriptNormV4_2Term
    manuscriptNormV4_2_exact_interval hq manuscriptNormV4_2_rounded_endpoints.1 manuscriptNormV4_2_rounded_endpoints.2
  have hw : ((2971062291974073186134220553 / 500000000000000000000000000000) - (5942124583948146371070298357 / 1000000000000000000000000000000) : ℚ) = (1198142749 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_3SubstituteRat_composition_error :
    |manuscriptNormV4_3Term - (manuscriptNormV4_3SubstituteRat : ℝ)| ≤ (((3095782879 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_3SubstituteRat ∈ Set.Icc manuscriptNormV4_3Interval.1 manuscriptNormV4_3Interval.2 := by
    simpa only [manuscriptNormV4_3SubstituteRat, manuscriptNormV4_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_3Interval.1 manuscriptNormV4_3Interval.2 manuscriptNormV4_3SubstituteRat
    (-15646810963972083306715065919 / 1000000000000000000000000000000) (-97792568524825520647620519 / 6250000000000000000000000000) manuscriptNormV4_3Term
    manuscriptNormV4_3_exact_interval hq manuscriptNormV4_3_rounded_endpoints.1 manuscriptNormV4_3_rounded_endpoints.2
  have hw : ((-97792568524825520647620519 / 6250000000000000000000000000) - (-15646810963972083306715065919 / 1000000000000000000000000000000) : ℚ) = (3095782879 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_4SubstituteRat_composition_error :
    |manuscriptNormV4_4Term - (manuscriptNormV4_4SubstituteRat : ℝ)| ≤ (((9114626057 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_4SubstituteRat ∈ Set.Icc manuscriptNormV4_4Interval.1 manuscriptNormV4_4Interval.2 := by
    simpa only [manuscriptNormV4_4SubstituteRat, manuscriptNormV4_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_4Interval.1 manuscriptNormV4_4Interval.2 manuscriptNormV4_4SubstituteRat
    (23284669083913738374859080853 / 500000000000000000000000000000) (46569338167827476758832787763 / 1000000000000000000000000000000) manuscriptNormV4_4Term
    manuscriptNormV4_4_exact_interval hq manuscriptNormV4_4_rounded_endpoints.1 manuscriptNormV4_4_rounded_endpoints.2
  have hw : ((46569338167827476758832787763 / 1000000000000000000000000000000) - (23284669083913738374859080853 / 500000000000000000000000000000) : ℚ) = (9114626057 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_5SubstituteRat_composition_error :
    |manuscriptNormV4_5Term - (manuscriptNormV4_5SubstituteRat : ℝ)| ≤ (((101210232537 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_5SubstituteRat ∈ Set.Icc manuscriptNormV4_5Interval.1 manuscriptNormV4_5Interval.2 := by
    simpa only [manuscriptNormV4_5SubstituteRat, manuscriptNormV4_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_5Interval.1 manuscriptNormV4_5Interval.2 manuscriptNormV4_5SubstituteRat
    (-18285074699575041905754917947 / 1000000000000000000000000000000) (-18285074699575041096073057651 / 1000000000000000000000000000000) manuscriptNormV4_5Term
    manuscriptNormV4_5_exact_interval hq manuscriptNormV4_5_rounded_endpoints.1 manuscriptNormV4_5_rounded_endpoints.2
  have hw : ((-18285074699575041096073057651 / 1000000000000000000000000000000) - (-18285074699575041905754917947 / 1000000000000000000000000000000) : ℚ) = (101210232537 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_6SubstituteRat_composition_error :
    |manuscriptNormV4_6Term - (manuscriptNormV4_6SubstituteRat : ℝ)| ≤ (((101210232537 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_6SubstituteRat ∈ Set.Icc manuscriptNormV4_6Interval.1 manuscriptNormV4_6Interval.2 := by
    simpa only [manuscriptNormV4_6SubstituteRat, manuscriptNormV4_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_6Interval.1 manuscriptNormV4_6Interval.2 manuscriptNormV4_6SubstituteRat
    (-18285074699575041905754917947 / 1000000000000000000000000000000) (-18285074699575041096073057651 / 1000000000000000000000000000000) manuscriptNormV4_6Term
    manuscriptNormV4_6_exact_interval hq manuscriptNormV4_6_rounded_endpoints.1 manuscriptNormV4_6_rounded_endpoints.2
  have hw : ((-18285074699575041096073057651 / 1000000000000000000000000000000) - (-18285074699575041905754917947 / 1000000000000000000000000000000) : ℚ) = (101210232537 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_7SubstituteRat_composition_error :
    |manuscriptNormV4_7Term - (manuscriptNormV4_7SubstituteRat : ℝ)| ≤ (((79469162947 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_7SubstituteRat ∈ Set.Icc manuscriptNormV4_7Interval.1 manuscriptNormV4_7Interval.2 := by
    simpa only [manuscriptNormV4_7SubstituteRat, manuscriptNormV4_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_7Interval.1 manuscriptNormV4_7Interval.2 manuscriptNormV4_7SubstituteRat
    (-7439891480413310489970227707 / 1000000000000000000000000000000) (-7439891480413309854216924131 / 1000000000000000000000000000000) manuscriptNormV4_7Term
    manuscriptNormV4_7_exact_interval hq manuscriptNormV4_7_rounded_endpoints.1 manuscriptNormV4_7_rounded_endpoints.2
  have hw : ((-7439891480413309854216924131 / 1000000000000000000000000000000) - (-7439891480413310489970227707 / 1000000000000000000000000000000) : ℚ) = (79469162947 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_8SubstituteRat_composition_error :
    |manuscriptNormV4_8Term - (manuscriptNormV4_8SubstituteRat : ℝ)| ≤ (((79469162947 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_8SubstituteRat ∈ Set.Icc manuscriptNormV4_8Interval.1 manuscriptNormV4_8Interval.2 := by
    simpa only [manuscriptNormV4_8SubstituteRat, manuscriptNormV4_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_8Interval.1 manuscriptNormV4_8Interval.2 manuscriptNormV4_8SubstituteRat
    (-7439891480413310489970227707 / 1000000000000000000000000000000) (-7439891480413309854216924131 / 1000000000000000000000000000000) manuscriptNormV4_8Term
    manuscriptNormV4_8_exact_interval hq manuscriptNormV4_8_rounded_endpoints.1 manuscriptNormV4_8_rounded_endpoints.2
  have hw : ((-7439891480413309854216924131 / 1000000000000000000000000000000) - (-7439891480413310489970227707 / 1000000000000000000000000000000) : ℚ) = (79469162947 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_9SubstituteRat_composition_error :
    |manuscriptNormV4_9Term - (manuscriptNormV4_9SubstituteRat : ℝ)| ≤ (((250873516999 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_9SubstituteRat ∈ Set.Icc manuscriptNormV4_9Interval.1 manuscriptNormV4_9Interval.2 := by
    simpa only [manuscriptNormV4_9SubstituteRat, manuscriptNormV4_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_9Interval.1 manuscriptNormV4_9Interval.2 manuscriptNormV4_9SubstituteRat
    (6450387944343331493548784039 / 1000000000000000000000000000000) (3225193972171665872211150519 / 500000000000000000000000000000) manuscriptNormV4_9Term
    manuscriptNormV4_9_exact_interval hq manuscriptNormV4_9_rounded_endpoints.1 manuscriptNormV4_9_rounded_endpoints.2
  have hw : ((3225193972171665872211150519 / 500000000000000000000000000000) - (6450387944343331493548784039 / 1000000000000000000000000000000) : ℚ) = (250873516999 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_10SubstituteRat_composition_error :
    |manuscriptNormV4_10Term - (manuscriptNormV4_10SubstituteRat : ℝ)| ≤ (((250873516999 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_10SubstituteRat ∈ Set.Icc manuscriptNormV4_10Interval.1 manuscriptNormV4_10Interval.2 := by
    simpa only [manuscriptNormV4_10SubstituteRat, manuscriptNormV4_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_10Interval.1 manuscriptNormV4_10Interval.2 manuscriptNormV4_10SubstituteRat
    (6450387944343331493548784039 / 1000000000000000000000000000000) (3225193972171665872211150519 / 500000000000000000000000000000) manuscriptNormV4_10Term
    manuscriptNormV4_10_exact_interval hq manuscriptNormV4_10_rounded_endpoints.1 manuscriptNormV4_10_rounded_endpoints.2
  have hw : ((3225193972171665872211150519 / 500000000000000000000000000000) - (6450387944343331493548784039 / 1000000000000000000000000000000) : ℚ) = (250873516999 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_11SubstituteRat_composition_error :
    |manuscriptNormV4_11Term - (manuscriptNormV4_11SubstituteRat : ℝ)| ≤ (((457333864503 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_11SubstituteRat ∈ Set.Icc manuscriptNormV4_11Interval.1 manuscriptNormV4_11Interval.2 := by
    simpa only [manuscriptNormV4_11SubstituteRat, manuscriptNormV4_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_11Interval.1 manuscriptNormV4_11Interval.2 manuscriptNormV4_11SubstituteRat
    (-5049556952780585057360689577 / 500000000000000000000000000000) (-10099113905561169657387514651 / 1000000000000000000000000000000) manuscriptNormV4_11Term
    manuscriptNormV4_11_exact_interval hq manuscriptNormV4_11_rounded_endpoints.1 manuscriptNormV4_11_rounded_endpoints.2
  have hw : ((-10099113905561169657387514651 / 1000000000000000000000000000000) - (-5049556952780585057360689577 / 500000000000000000000000000000) : ℚ) = (457333864503 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV4_12SubstituteRat_composition_error :
    |manuscriptNormV4_12Term - (manuscriptNormV4_12SubstituteRat : ℝ)| ≤ (((457333864503 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV4_12SubstituteRat ∈ Set.Icc manuscriptNormV4_12Interval.1 manuscriptNormV4_12Interval.2 := by
    simpa only [manuscriptNormV4_12SubstituteRat, manuscriptNormV4_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV4_12Interval.1 manuscriptNormV4_12Interval.2 manuscriptNormV4_12SubstituteRat
    (-5049556952780585057360689577 / 500000000000000000000000000000) (-10099113905561169657387514651 / 1000000000000000000000000000000) manuscriptNormV4_12Term
    manuscriptNormV4_12_exact_interval hq manuscriptNormV4_12_rounded_endpoints.1 manuscriptNormV4_12_rounded_endpoints.2
  have hw : ((-10099113905561169657387514651 / 1000000000000000000000000000000) - (-5049556952780585057360689577 / 500000000000000000000000000000) : ℚ) = (457333864503 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow4_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 4 (0, 0)) - (manuscriptNormVSubstituteRow4 : ℝ)| ≤ (((4322254041523 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV4_0SubstituteRat_composition_error
  have h1 := manuscriptNormV4_1SubstituteRat_composition_error
  have h2 := manuscriptNormV4_2SubstituteRat_composition_error
  have h3 := manuscriptNormV4_3SubstituteRat_composition_error
  have h4 := manuscriptNormV4_4SubstituteRat_composition_error
  have h5 := manuscriptNormV4_5SubstituteRat_composition_error
  have h6 := manuscriptNormV4_6SubstituteRat_composition_error
  have h7 := manuscriptNormV4_7SubstituteRat_composition_error
  have h8 := manuscriptNormV4_8SubstituteRat_composition_error
  have h9 := manuscriptNormV4_9SubstituteRat_composition_error
  have h10 := manuscriptNormV4_10SubstituteRat_composition_error
  have h11 := manuscriptNormV4_11SubstituteRat_composition_error
  have h12 := manuscriptNormV4_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV4_0Term + (manuscriptNormV4_1Term + (manuscriptNormV4_2Term + (manuscriptNormV4_3Term + (manuscriptNormV4_4Term + (manuscriptNormV4_5Term + (manuscriptNormV4_6Term + (manuscriptNormV4_7Term + (manuscriptNormV4_8Term + (manuscriptNormV4_9Term + (manuscriptNormV4_10Term + (manuscriptNormV4_11Term + (manuscriptNormV4_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow4 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow4
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

def manuscriptNormV4_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1)

private theorem manuscriptNormV4_0RoundedSubstituteRat_error :
    |(manuscriptNormV4_0SubstituteRat : ℝ) - (manuscriptNormV4_0RoundedSubstituteRat : ℝ)| ≤
      (((176586819674127 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-176586819674127 / 10000000000000000) (0 / 1) (1) (0) (1247689 / 781250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-176586819674127 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((176586819674127 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1)

private theorem manuscriptNormV4_1RoundedSubstituteRat_error :
    |(manuscriptNormV4_1SubstituteRat : ℝ) - (manuscriptNormV4_1RoundedSubstituteRat : ℝ)| ≤
      (((25860054013467 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-25860054013467 / 5000000000000000) (0 / 1) (1) (0) (36929929 / 19531250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-25860054013467 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((25860054013467 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1)

private theorem manuscriptNormV4_2RoundedSubstituteRat_error :
    |(manuscriptNormV4_2SubstituteRat : ℝ) - (manuscriptNormV4_2RoundedSubstituteRat : ℝ)| ≤
      (((14786416795743 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-14786416795743 / 5000000000000000) (0 / 1) (-6) (0) (11235904 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-14786416795743 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((14786416795743 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1)

private theorem manuscriptNormV4_3RoundedSubstituteRat_error :
    |(manuscriptNormV4_3SubstituteRat : ℝ) - (manuscriptNormV4_3RoundedSubstituteRat : ℝ)| ≤
      (((28654058117769 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (28654058117769 / 5000000000000000) (0 / 1) (-8) (0) (425104 / 390625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((28654058117769 / 5000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((28654058117769 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV4_4RoundedSubstituteRat_error :
    |(manuscriptNormV4_4SubstituteRat : ℝ) - (manuscriptNormV4_4RoundedSubstituteRat : ℝ)| ≤
      (((134981572076649 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-134981572076649 / 10000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-134981572076649 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((134981572076649 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV4_5RoundedSubstituteRat_error :
    |(manuscriptNormV4_5SubstituteRat : ℝ) - (manuscriptNormV4_5RoundedSubstituteRat : ℝ)| ≤
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num) (by norm_num)
  have hw : |(((-158231827865049 / 10000000000000000) : ℚ) : ℝ)| + |(((-6979596199593 / 312500000000000) : ℚ) : ℝ)| =
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047)

private theorem manuscriptNormV4_6RoundedSubstituteRat_error :
    |(manuscriptNormV4_6SubstituteRat : ℝ) - (manuscriptNormV4_6RoundedSubstituteRat : ℝ)| ≤
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-158231827865049 / 10000000000000000) (6979596199593 / 312500000000000) (0) (1) (62073709 / 39062500) (-1453 / 11047) (by norm_num) (by norm_num)
  have hw : |(((-158231827865049 / 10000000000000000) : ℚ) : ℝ)| + |(((6979596199593 / 312500000000000) : ℚ) : ℝ)| =
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357)

private theorem manuscriptNormV4_7RoundedSubstituteRat_error :
    |(manuscriptNormV4_7SubstituteRat : ℝ) - (manuscriptNormV4_7RoundedSubstituteRat : ℝ)| ≤
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357) (by norm_num) (by norm_num)
  have hw : |(((91031408615547 / 5000000000000000) : ℚ) : ℝ)| + |(((-175369027693701 / 10000000000000000) : ℚ) : ℝ)| =
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV4_8RoundedSubstituteRat_error :
    |(manuscriptNormV4_8SubstituteRat : ℝ) - (manuscriptNormV4_8RoundedSubstituteRat : ℝ)| ≤
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357) (by norm_num) (by norm_num)
  have hw : |(((91031408615547 / 5000000000000000) : ℚ) : ℝ)| + |(((175369027693701 / 10000000000000000) : ℚ) : ℝ)| =
      (((71486368984959 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493)

private theorem manuscriptNormV4_9RoundedSubstituteRat_error :
    |(manuscriptNormV4_9SubstituteRat : ℝ) - (manuscriptNormV4_9RoundedSubstituteRat : ℝ)| ≤
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493) (by norm_num) (by norm_num)
  have hw : |(((38883310921047 / 10000000000000000) : ℚ) : ℝ)| + |(((69199218597939 / 10000000000000000) : ℚ) : ℝ)| =
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV4_10RoundedSubstituteRat_error :
    |(manuscriptNormV4_10SubstituteRat : ℝ) - (manuscriptNormV4_10RoundedSubstituteRat : ℝ)| ≤
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num) (by norm_num)
  have hw : |(((38883310921047 / 10000000000000000) : ℚ) : ℝ)| + |(((-69199218597939 / 10000000000000000) : ℚ) : ℝ)| =
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV4_11RoundedSubstituteRat_error :
    |(manuscriptNormV4_11SubstituteRat : ℝ) - (manuscriptNormV4_11RoundedSubstituteRat : ℝ)| ≤
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377) (by norm_num) (by norm_num)
  have hw : |(((-23877787302441 / 20000000000000000) : ℚ) : ℝ)| + |(((-252298143070293 / 20000000000000000) : ℚ) : ℝ)| =
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV4_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV4_12RoundedSubstituteRat_error :
    |(manuscriptNormV4_12SubstituteRat : ℝ) - (manuscriptNormV4_12RoundedSubstituteRat : ℝ)| ≤
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377) (by norm_num) (by norm_num)
  have hw : |(((-23877787302441 / 20000000000000000) : ℚ) : ℝ)| + |(((252298143070293 / 20000000000000000) : ℚ) : ℝ)| =
      (((138087965186367 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow4 : ℚ :=
  manuscriptNormV4_0RoundedSubstituteRat +
    manuscriptNormV4_1RoundedSubstituteRat +
    manuscriptNormV4_2RoundedSubstituteRat +
    manuscriptNormV4_3RoundedSubstituteRat +
    manuscriptNormV4_4RoundedSubstituteRat +
    manuscriptNormV4_5RoundedSubstituteRat +
    manuscriptNormV4_6RoundedSubstituteRat +
    manuscriptNormV4_7RoundedSubstituteRat +
    manuscriptNormV4_8RoundedSubstituteRat +
    manuscriptNormV4_9RoundedSubstituteRat +
    manuscriptNormV4_10RoundedSubstituteRat +
    manuscriptNormV4_11RoundedSubstituteRat +
    manuscriptNormV4_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow4_error :
    |(manuscriptNormVSubstituteRow4 : ℝ) - (manuscriptNormVRoundedSubstituteRow4 : ℝ)| ≤
      (((60513298534227 / 250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV4_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV4_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV4_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV4_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV4_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV4_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV4_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV4_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV4_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV4_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV4_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV4_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV4_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow4 manuscriptNormVRoundedSubstituteRow4
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

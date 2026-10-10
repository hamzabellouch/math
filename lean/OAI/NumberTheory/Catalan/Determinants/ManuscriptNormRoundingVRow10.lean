import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup043
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup044
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup045
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup046
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup047
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV10_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV10_0SubstituteRat_interval :
    manuscriptNormV10_0SubstituteRat ∈ Set.Icc manuscriptNormV10_0Interval.1 manuscriptNormV10_0Interval.2 := by
  simpa only [manuscriptNormV10_0SubstituteRat, manuscriptNormV10_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num))

private theorem manuscriptNormV10_0SubstituteRat_upper :
    manuscriptNormV10_0SubstituteRat ≤ (-592090129958566250568464173 / 125000000000000000000000000000) :=
  manuscriptNormV10_0SubstituteRat_interval.2.trans manuscriptNormV10_0_rounded_endpoints.2

def manuscriptNormV10_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV10_1SubstituteRat_interval :
    manuscriptNormV10_1SubstituteRat ∈ Set.Icc manuscriptNormV10_1Interval.1 manuscriptNormV10_1Interval.2 := by
  simpa only [manuscriptNormV10_1SubstituteRat, manuscriptNormV10_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num))

private theorem manuscriptNormV10_1SubstituteRat_upper :
    manuscriptNormV10_1SubstituteRat ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) :=
  manuscriptNormV10_1SubstituteRat_interval.2.trans manuscriptNormV10_1_rounded_endpoints.2

def manuscriptNormV10_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV10_2SubstituteRat_interval :
    manuscriptNormV10_2SubstituteRat ∈ Set.Icc manuscriptNormV10_2Interval.1 manuscriptNormV10_2Interval.2 := by
  simpa only [manuscriptNormV10_2SubstituteRat, manuscriptNormV10_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num))

private theorem manuscriptNormV10_2SubstituteRat_upper :
    manuscriptNormV10_2SubstituteRat ≤ (643579885822160983031310613 / 500000000000000000000000000000) :=
  manuscriptNormV10_2SubstituteRat_interval.2.trans manuscriptNormV10_2_rounded_endpoints.2

def manuscriptNormV10_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV10_3SubstituteRat_interval :
    manuscriptNormV10_3SubstituteRat ∈ Set.Icc manuscriptNormV10_3Interval.1 manuscriptNormV10_3Interval.2 := by
  simpa only [manuscriptNormV10_3SubstituteRat, manuscriptNormV10_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num))

private theorem manuscriptNormV10_3SubstituteRat_upper :
    manuscriptNormV10_3SubstituteRat ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) :=
  manuscriptNormV10_3SubstituteRat_interval.2.trans manuscriptNormV10_3_rounded_endpoints.2

def manuscriptNormV10_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV10_4SubstituteRat_interval :
    manuscriptNormV10_4SubstituteRat ∈ Set.Icc manuscriptNormV10_4Interval.1 manuscriptNormV10_4Interval.2 := by
  simpa only [manuscriptNormV10_4SubstituteRat, manuscriptNormV10_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num))

private theorem manuscriptNormV10_4SubstituteRat_upper :
    manuscriptNormV10_4SubstituteRat ≤ (3225193972171665872211150519 / 500000000000000000000000000000) :=
  manuscriptNormV10_4SubstituteRat_interval.2.trans manuscriptNormV10_4_rounded_endpoints.2

def manuscriptNormV10_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV10_5SubstituteRat_interval :
    manuscriptNormV10_5SubstituteRat ∈ Set.Icc manuscriptNormV10_5Interval.1 manuscriptNormV10_5Interval.2 := by
  simpa only [manuscriptNormV10_5SubstituteRat, manuscriptNormV10_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_5SubstituteRat_upper :
    manuscriptNormV10_5SubstituteRat ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) :=
  manuscriptNormV10_5SubstituteRat_interval.2.trans manuscriptNormV10_5_rounded_endpoints.2

def manuscriptNormV10_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV10_6SubstituteRat_interval :
    manuscriptNormV10_6SubstituteRat ∈ Set.Icc manuscriptNormV10_6Interval.1 manuscriptNormV10_6Interval.2 := by
  simpa only [manuscriptNormV10_6SubstituteRat, manuscriptNormV10_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_6SubstituteRat_upper :
    manuscriptNormV10_6SubstituteRat ≤ (-767346206193196360302151557 / 200000000000000000000000000000) :=
  manuscriptNormV10_6SubstituteRat_interval.2.trans manuscriptNormV10_6_rounded_endpoints.2

def manuscriptNormV10_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV10_7SubstituteRat_interval :
    manuscriptNormV10_7SubstituteRat ∈ Set.Icc manuscriptNormV10_7Interval.1 manuscriptNormV10_7Interval.2 := by
  simpa only [manuscriptNormV10_7SubstituteRat, manuscriptNormV10_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_7SubstituteRat_upper :
    manuscriptNormV10_7SubstituteRat ≤ (-735139122654920217587852529 / 100000000000000000000000000000) :=
  manuscriptNormV10_7SubstituteRat_interval.2.trans manuscriptNormV10_7_rounded_endpoints.2

def manuscriptNormV10_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV10_8SubstituteRat_interval :
    manuscriptNormV10_8SubstituteRat ∈ Set.Icc manuscriptNormV10_8Interval.1 manuscriptNormV10_8Interval.2 := by
  simpa only [manuscriptNormV10_8SubstituteRat, manuscriptNormV10_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_8SubstituteRat_upper :
    manuscriptNormV10_8SubstituteRat ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) :=
  manuscriptNormV10_8SubstituteRat_interval.2.trans manuscriptNormV10_8_rounded_endpoints.2

def manuscriptNormV10_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1)

private theorem manuscriptNormV10_9SubstituteRat_interval :
    manuscriptNormV10_9SubstituteRat ∈ Set.Icc manuscriptNormV10_9Interval.1 manuscriptNormV10_9Interval.2 := by
  simpa only [manuscriptNormV10_9SubstituteRat, manuscriptNormV10_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_9SubstituteRat_upper :
    manuscriptNormV10_9SubstituteRat ≤ (11345626425745525020670345831 / 1000000000000000000000000000000) :=
  manuscriptNormV10_9SubstituteRat_interval.2.trans manuscriptNormV10_9_rounded_endpoints.2

def manuscriptNormV10_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1)

private theorem manuscriptNormV10_10SubstituteRat_interval :
    manuscriptNormV10_10SubstituteRat ∈ Set.Icc manuscriptNormV10_10Interval.1 manuscriptNormV10_10Interval.2 := by
  simpa only [manuscriptNormV10_10SubstituteRat, manuscriptNormV10_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_10SubstituteRat_upper :
    manuscriptNormV10_10SubstituteRat ≤ (1573387720016090158299731593 / 1000000000000000000000000000000) :=
  manuscriptNormV10_10SubstituteRat_interval.2.trans manuscriptNormV10_10_rounded_endpoints.2

def manuscriptNormV10_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV10_11SubstituteRat_interval :
    manuscriptNormV10_11SubstituteRat ∈ Set.Icc manuscriptNormV10_11Interval.1 manuscriptNormV10_11Interval.2 := by
  simpa only [manuscriptNormV10_11SubstituteRat, manuscriptNormV10_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_11SubstituteRat_upper :
    manuscriptNormV10_11SubstituteRat ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) :=
  manuscriptNormV10_11SubstituteRat_interval.2.trans manuscriptNormV10_11_rounded_endpoints.2

def manuscriptNormV10_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV10_12SubstituteRat_interval :
    manuscriptNormV10_12SubstituteRat ∈ Set.Icc manuscriptNormV10_12Interval.1 manuscriptNormV10_12Interval.2 := by
  simpa only [manuscriptNormV10_12SubstituteRat, manuscriptNormV10_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV10_12SubstituteRat_upper :
    manuscriptNormV10_12SubstituteRat ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) :=
  manuscriptNormV10_12SubstituteRat_interval.2.trans manuscriptNormV10_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow10 : ℚ :=
  manuscriptNormV10_0SubstituteRat +
    manuscriptNormV10_1SubstituteRat +
    manuscriptNormV10_2SubstituteRat +
    manuscriptNormV10_3SubstituteRat +
    manuscriptNormV10_4SubstituteRat +
    manuscriptNormV10_5SubstituteRat +
    manuscriptNormV10_6SubstituteRat +
    manuscriptNormV10_7SubstituteRat +
    manuscriptNormV10_8SubstituteRat +
    manuscriptNormV10_9SubstituteRat +
    manuscriptNormV10_10SubstituteRat +
    manuscriptNormV10_11SubstituteRat +
    manuscriptNormV10_12SubstituteRat

theorem manuscriptNormVSubstituteRow10_upper : manuscriptNormVSubstituteRow10 ≤ (-13331960711348427692491383349 / 250000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow10
  linarith only [manuscriptNormV10_0SubstituteRat_upper,
    manuscriptNormV10_1SubstituteRat_upper,
    manuscriptNormV10_2SubstituteRat_upper,
    manuscriptNormV10_3SubstituteRat_upper,
    manuscriptNormV10_4SubstituteRat_upper,
    manuscriptNormV10_5SubstituteRat_upper,
    manuscriptNormV10_6SubstituteRat_upper,
    manuscriptNormV10_7SubstituteRat_upper,
    manuscriptNormV10_8SubstituteRat_upper,
    manuscriptNormV10_9SubstituteRat_upper,
    manuscriptNormV10_10SubstituteRat_upper,
    manuscriptNormV10_11SubstituteRat_upper,
    manuscriptNormV10_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV10_0SubstituteRat_composition_error :
    |manuscriptNormV10_0Term - (manuscriptNormV10_0SubstituteRat : ℝ)| ≤ (((41023162771 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_0SubstituteRat ∈ Set.Icc manuscriptNormV10_0Interval.1 manuscriptNormV10_0Interval.2 := by
    simpa only [manuscriptNormV10_0SubstituteRat, manuscriptNormV10_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_0Interval.1 manuscriptNormV10_0Interval.2 manuscriptNormV10_0SubstituteRat
    (-9251408280602598306119171 / 1953125000000000000000000000) (-592090129958566250568464173 / 125000000000000000000000000000) manuscriptNormV10_0Term
    manuscriptNormV10_0_exact_interval hq manuscriptNormV10_0_rounded_endpoints.1 manuscriptNormV10_0_rounded_endpoints.2
  have hw : ((-592090129958566250568464173 / 125000000000000000000000000000) - (-9251408280602598306119171 / 1953125000000000000000000000) : ℚ) = (41023162771 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_1SubstituteRat_composition_error :
    |manuscriptNormV10_1Term - (manuscriptNormV10_1SubstituteRat : ℝ)| ≤ (((24030658553 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_1SubstituteRat ∈ Set.Icc manuscriptNormV10_1Interval.1 manuscriptNormV10_1Interval.2 := by
    simpa only [manuscriptNormV10_1SubstituteRat, manuscriptNormV10_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_1Interval.1 manuscriptNormV10_1Interval.2 manuscriptNormV10_1SubstituteRat
    (-1512993449261219836137063493 / 1000000000000000000000000000000) (-1512993449261219740014429281 / 1000000000000000000000000000000) manuscriptNormV10_1Term
    manuscriptNormV10_1_exact_interval hq manuscriptNormV10_1_rounded_endpoints.1 manuscriptNormV10_1_rounded_endpoints.2
  have hw : ((-1512993449261219740014429281 / 1000000000000000000000000000000) - (-1512993449261219836137063493 / 1000000000000000000000000000000) : ℚ) = (24030658553 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_2SubstituteRat_composition_error :
    |manuscriptNormV10_2Term - (manuscriptNormV10_2SubstituteRat : ℝ)| ≤ (((3435056221 / 62500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_2SubstituteRat ∈ Set.Icc manuscriptNormV10_2Interval.1 manuscriptNormV10_2Interval.2 := by
    simpa only [manuscriptNormV10_2SubstituteRat, manuscriptNormV10_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_2Interval.1 manuscriptNormV10_2Interval.2 manuscriptNormV10_2SubstituteRat
    (128715977164432191110172169 / 100000000000000000000000000000) (643579885822160983031310613 / 500000000000000000000000000000) manuscriptNormV10_2Term
    manuscriptNormV10_2_exact_interval hq manuscriptNormV10_2_rounded_endpoints.1 manuscriptNormV10_2_rounded_endpoints.2
  have hw : ((643579885822160983031310613 / 500000000000000000000000000000) - (128715977164432191110172169 / 100000000000000000000000000000) : ℚ) = (3435056221 / 62500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_3SubstituteRat_composition_error :
    |manuscriptNormV10_3Term - (manuscriptNormV10_3SubstituteRat : ℝ)| ≤ (((106507475189 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_3SubstituteRat ∈ Set.Icc manuscriptNormV10_3Interval.1 manuscriptNormV10_3Interval.2 := by
    simpa only [manuscriptNormV10_3SubstituteRat, manuscriptNormV10_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_3Interval.1 manuscriptNormV10_3Interval.2 manuscriptNormV10_3SubstituteRat
    (-1330194736875770427300979589 / 500000000000000000000000000000) (-2660389473751540748094483989 / 1000000000000000000000000000000) manuscriptNormV10_3Term
    manuscriptNormV10_3_exact_interval hq manuscriptNormV10_3_rounded_endpoints.1 manuscriptNormV10_3_rounded_endpoints.2
  have hw : ((-2660389473751540748094483989 / 1000000000000000000000000000000) - (-1330194736875770427300979589 / 500000000000000000000000000000) : ℚ) = (106507475189 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_4SubstituteRat_composition_error :
    |manuscriptNormV10_4Term - (manuscriptNormV10_4SubstituteRat : ℝ)| ≤ (((250873516999 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_4SubstituteRat ∈ Set.Icc manuscriptNormV10_4Interval.1 manuscriptNormV10_4Interval.2 := by
    simpa only [manuscriptNormV10_4SubstituteRat, manuscriptNormV10_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_4Interval.1 manuscriptNormV10_4Interval.2 manuscriptNormV10_4SubstituteRat
    (6450387944343331493548784039 / 1000000000000000000000000000000) (3225193972171665872211150519 / 500000000000000000000000000000) manuscriptNormV10_4Term
    manuscriptNormV10_4_exact_interval hq manuscriptNormV10_4_rounded_endpoints.1 manuscriptNormV10_4_rounded_endpoints.2
  have hw : ((3225193972171665872211150519 / 500000000000000000000000000000) - (6450387944343331493548784039 / 1000000000000000000000000000000) : ℚ) = (250873516999 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_5SubstituteRat_composition_error :
    |manuscriptNormV10_5Term - (manuscriptNormV10_5SubstituteRat : ℝ)| ≤ (((2161896379 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_5SubstituteRat ∈ Set.Icc manuscriptNormV10_5Interval.1 manuscriptNormV10_5Interval.2 := by
    simpa only [manuscriptNormV10_5SubstituteRat, manuscriptNormV10_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_5Interval.1 manuscriptNormV10_5Interval.2 manuscriptNormV10_5SubstituteRat
    (-2733586989958455530919248339 / 125000000000000000000000000000) (-10934347959833822121515096977 / 500000000000000000000000000000) manuscriptNormV10_5Term
    manuscriptNormV10_5_exact_interval hq manuscriptNormV10_5_rounded_endpoints.1 manuscriptNormV10_5_rounded_endpoints.2
  have hw : ((-10934347959833822121515096977 / 500000000000000000000000000000) - (-2733586989958455530919248339 / 125000000000000000000000000000) : ℚ) = (2161896379 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_6SubstituteRat_composition_error :
    |manuscriptNormV10_6Term - (manuscriptNormV10_6SubstituteRat : ℝ)| ≤ (((232689437 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_6SubstituteRat ∈ Set.Icc manuscriptNormV10_6Interval.1 manuscriptNormV10_6Interval.2 := by
    simpa only [manuscriptNormV10_6SubstituteRat, manuscriptNormV10_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_6Interval.1 manuscriptNormV10_6Interval.2 manuscriptNormV10_6SubstituteRat
    (-3836731030965981801976136659 / 1000000000000000000000000000000) (-767346206193196360302151557 / 200000000000000000000000000000) manuscriptNormV10_6Term
    manuscriptNormV10_6_exact_interval hq manuscriptNormV10_6_rounded_endpoints.1 manuscriptNormV10_6_rounded_endpoints.2
  have hw : ((-767346206193196360302151557 / 200000000000000000000000000000) - (-3836731030965981801976136659 / 1000000000000000000000000000000) : ℚ) = (232689437 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_7SubstituteRat_composition_error :
    |manuscriptNormV10_7Term - (manuscriptNormV10_7SubstituteRat : ℝ)| ≤ (((758813281 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_7SubstituteRat ∈ Set.Icc manuscriptNormV10_7Interval.1 manuscriptNormV10_7Interval.2 := by
    simpa only [manuscriptNormV10_7SubstituteRat, manuscriptNormV10_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_7Interval.1 manuscriptNormV10_7Interval.2 manuscriptNormV10_7SubstituteRat
    (-1837847806637300544349037963 / 250000000000000000000000000000) (-735139122654920217587852529 / 100000000000000000000000000000) manuscriptNormV10_7Term
    manuscriptNormV10_7_exact_interval hq manuscriptNormV10_7_rounded_endpoints.1 manuscriptNormV10_7_rounded_endpoints.2
  have hw : ((-735139122654920217587852529 / 100000000000000000000000000000) - (-1837847806637300544349037963 / 250000000000000000000000000000) : ℚ) = (758813281 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_8SubstituteRat_composition_error :
    |manuscriptNormV10_8Term - (manuscriptNormV10_8SubstituteRat : ℝ)| ≤ (((480735149 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_8SubstituteRat ∈ Set.Icc manuscriptNormV10_8Interval.1 manuscriptNormV10_8Interval.2 := by
    simpa only [manuscriptNormV10_8SubstituteRat, manuscriptNormV10_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_8Interval.1 manuscriptNormV10_8Interval.2 manuscriptNormV10_8SubstituteRat
    (-2207517269453298436964373209 / 250000000000000000000000000000) (-4415034538906596873448011269 / 500000000000000000000000000000) manuscriptNormV10_8Term
    manuscriptNormV10_8_exact_interval hq manuscriptNormV10_8_rounded_endpoints.1 manuscriptNormV10_8_rounded_endpoints.2
  have hw : ((-4415034538906596873448011269 / 500000000000000000000000000000) - (-2207517269453298436964373209 / 250000000000000000000000000000) : ℚ) = (480735149 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_9SubstituteRat_composition_error :
    |manuscriptNormV10_9Term - (manuscriptNormV10_9SubstituteRat : ℝ)| ≤ (((2718591633 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_9SubstituteRat ∈ Set.Icc manuscriptNormV10_9Interval.1 manuscriptNormV10_9Interval.2 := by
    simpa only [manuscriptNormV10_9SubstituteRat, manuscriptNormV10_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_9Interval.1 manuscriptNormV10_9Interval.2 manuscriptNormV10_9SubstituteRat
    (5672813212872762508975877099 / 500000000000000000000000000000) (11345626425745525020670345831 / 1000000000000000000000000000000) manuscriptNormV10_9Term
    manuscriptNormV10_9_exact_interval hq manuscriptNormV10_9_rounded_endpoints.1 manuscriptNormV10_9_rounded_endpoints.2
  have hw : ((11345626425745525020670345831 / 1000000000000000000000000000000) - (5672813212872762508975877099 / 500000000000000000000000000000) : ℚ) = (2718591633 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_10SubstituteRat_composition_error :
    |manuscriptNormV10_10Term - (manuscriptNormV10_10SubstituteRat : ℝ)| ≤ (((165223607 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_10SubstituteRat ∈ Set.Icc manuscriptNormV10_10Interval.1 manuscriptNormV10_10Interval.2 := by
    simpa only [manuscriptNormV10_10SubstituteRat, manuscriptNormV10_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_10Interval.1 manuscriptNormV10_10Interval.2 manuscriptNormV10_10SubstituteRat
    (786693860008045079067253993 / 500000000000000000000000000000) (1573387720016090158299731593 / 1000000000000000000000000000000) manuscriptNormV10_10Term
    manuscriptNormV10_10_exact_interval hq manuscriptNormV10_10_rounded_endpoints.1 manuscriptNormV10_10_rounded_endpoints.2
  have hw : ((1573387720016090158299731593 / 1000000000000000000000000000000) - (786693860008045079067253993 / 500000000000000000000000000000) : ℚ) = (165223607 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_11SubstituteRat_composition_error :
    |manuscriptNormV10_11Term - (manuscriptNormV10_11SubstituteRat : ℝ)| ≤ (((4149300417 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_11SubstituteRat ∈ Set.Icc manuscriptNormV10_11Interval.1 manuscriptNormV10_11Interval.2 := by
    simpa only [manuscriptNormV10_11SubstituteRat, manuscriptNormV10_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_11Interval.1 manuscriptNormV10_11Interval.2 manuscriptNormV10_11SubstituteRat
    (-9565262706655637646952898537 / 500000000000000000000000000000) (-19130525413311275289756496657 / 1000000000000000000000000000000) manuscriptNormV10_11Term
    manuscriptNormV10_11_exact_interval hq manuscriptNormV10_11_rounded_endpoints.1 manuscriptNormV10_11_rounded_endpoints.2
  have hw : ((-19130525413311275289756496657 / 1000000000000000000000000000000) - (-9565262706655637646952898537 / 500000000000000000000000000000) : ℚ) = (4149300417 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV10_12SubstituteRat_composition_error :
    |manuscriptNormV10_12Term - (manuscriptNormV10_12SubstituteRat : ℝ)| ≤ (((215141891 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV10_12SubstituteRat ∈ Set.Icc manuscriptNormV10_12Interval.1 manuscriptNormV10_12Interval.2 := by
    simpa only [manuscriptNormV10_12SubstituteRat, manuscriptNormV10_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV10_12Interval.1 manuscriptNormV10_12Interval.2 manuscriptNormV10_12SubstituteRat
    (-1014222019038597977530548497 / 250000000000000000000000000000) (-2028444038077195954845955103 / 500000000000000000000000000000) manuscriptNormV10_12Term
    manuscriptNormV10_12_exact_interval hq manuscriptNormV10_12_rounded_endpoints.1 manuscriptNormV10_12_rounded_endpoints.2
  have hw : ((-2028444038077195954845955103 / 500000000000000000000000000000) - (-1014222019038597977530548497 / 250000000000000000000000000000) : ℚ) = (215141891 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow10_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 10 (0, 0)) - (manuscriptNormVSubstituteRow10 : ℝ)| ≤ (((170276299207 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV10_0SubstituteRat_composition_error
  have h1 := manuscriptNormV10_1SubstituteRat_composition_error
  have h2 := manuscriptNormV10_2SubstituteRat_composition_error
  have h3 := manuscriptNormV10_3SubstituteRat_composition_error
  have h4 := manuscriptNormV10_4SubstituteRat_composition_error
  have h5 := manuscriptNormV10_5SubstituteRat_composition_error
  have h6 := manuscriptNormV10_6SubstituteRat_composition_error
  have h7 := manuscriptNormV10_7SubstituteRat_composition_error
  have h8 := manuscriptNormV10_8SubstituteRat_composition_error
  have h9 := manuscriptNormV10_9SubstituteRat_composition_error
  have h10 := manuscriptNormV10_10SubstituteRat_composition_error
  have h11 := manuscriptNormV10_11SubstituteRat_composition_error
  have h12 := manuscriptNormV10_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV10_0Term + (manuscriptNormV10_1Term + (manuscriptNormV10_2Term + (manuscriptNormV10_3Term + (manuscriptNormV10_4Term + (manuscriptNormV10_5Term + (manuscriptNormV10_6Term + (manuscriptNormV10_7Term + (manuscriptNormV10_8Term + (manuscriptNormV10_9Term + (manuscriptNormV10_10Term + (manuscriptNormV10_11Term + (manuscriptNormV10_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow10 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow10
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

def manuscriptNormV10_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV10_0RoundedSubstituteRat_error :
    |(manuscriptNormV10_0SubstituteRat : ℝ) - (manuscriptNormV10_0RoundedSubstituteRat : ℝ)| ≤
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441) (by norm_num) (by norm_num)
  have hw : |(((50868278597681 / 10000000000000000) : ℚ) : ℝ)| + |(((-90528431015797 / 10000000000000000) : ℚ) : ℝ)| =
      (((70698354806739 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV10_1RoundedSubstituteRat_error :
    |(manuscriptNormV10_1SubstituteRat : ℝ) - (manuscriptNormV10_1RoundedSubstituteRat : ℝ)| ≤
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599) (by norm_num) (by norm_num)
  have hw : |(((7449346641701 / 5000000000000000) : ℚ) : ℝ)| + |(((-13257332116537 / 5000000000000000) : ℚ) : ℝ)| =
      (((10353339379119 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV10_2RoundedSubstituteRat_error :
    |(manuscriptNormV10_2SubstituteRat : ℝ) - (manuscriptNormV10_2RoundedSubstituteRat : ℝ)| ≤
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601) (by norm_num) (by norm_num)
  have hw : |(((4259432104929 / 5000000000000000) : ℚ) : ℝ)| + |(((-7580356876773 / 5000000000000000) : ℚ) : ℝ)| =
      (((5919894490851 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV10_3RoundedSubstituteRat_error :
    |(manuscriptNormV10_3SubstituteRat : ℝ) - (manuscriptNormV10_3RoundedSubstituteRat : ℝ)| ≤
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629) (by norm_num) (by norm_num)
  have hw : |(((-8254198212407 / 5000000000000000) : ℚ) : ℝ)| + |(((14689697274259 / 5000000000000000) : ℚ) : ℝ)| =
      (((11471947743333 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV10_4RoundedSubstituteRat_error :
    |(manuscriptNormV10_4SubstituteRat : ℝ) - (manuscriptNormV10_4RoundedSubstituteRat : ℝ)| ≤
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493) (by norm_num) (by norm_num)
  have hw : |(((38883310921047 / 10000000000000000) : ℚ) : ℝ)| + |(((-69199218597939 / 10000000000000000) : ℚ) : ℝ)| =
      (((54041264759493 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV10_5RoundedSubstituteRat_error :
    |(manuscriptNormV10_5SubstituteRat : ℝ) - (manuscriptNormV10_5RoundedSubstituteRat : ℝ)| ≤
      (((88430832620597 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((160081263898183 / 10000000000000000) : ℚ) : ℝ)| + |(((-16780401343011 / 10000000000000000) : ℚ) : ℝ)| =
      (((88430832620597 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV10_6RoundedSubstituteRat_error :
    |(manuscriptNormV10_6SubstituteRat : ℝ) - (manuscriptNormV10_6RoundedSubstituteRat : ℝ)| ≤
      (((53594091090839 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-68919525805689 / 10000000000000000) : ℚ) : ℝ)| + |(((-145456838557667 / 10000000000000000) : ℚ) : ℝ)| =
      (((53594091090839 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV10_7RoundedSubstituteRat_error :
    |(manuscriptNormV10_7SubstituteRat : ℝ) - (manuscriptNormV10_7RoundedSubstituteRat : ℝ)| ≤
      (((90655810620933 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((37458406176029 / 10000000000000000) : ℚ) : ℝ)| + |(((143853215065837 / 10000000000000000) : ℚ) : ℝ)| =
      (((90655810620933 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV10_8RoundedSubstituteRat_error :
    |(manuscriptNormV10_8SubstituteRat : ℝ) - (manuscriptNormV10_8RoundedSubstituteRat : ℝ)| ≤
      (((23146012346453 / 1250000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-142349837215793 / 10000000000000000) : ℚ) : ℝ)| + |(((42818261555831 / 10000000000000000) : ℚ) : ℝ)| =
      (((23146012346453 / 1250000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1)

private theorem manuscriptNormV10_9RoundedSubstituteRat_error :
    |(manuscriptNormV10_9SubstituteRat : ℝ) - (manuscriptNormV10_9RoundedSubstituteRat : ℝ)| ≤
      (((4667632496657 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-4667632496657 / 1000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((4667632496657 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1)

private theorem manuscriptNormV10_10RoundedSubstituteRat_error :
    |(manuscriptNormV10_10SubstituteRat : ℝ) - (manuscriptNormV10_10RoundedSubstituteRat : ℝ)| ≤
      (((32071079472761 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((3034321589211 / 1250000000000000) : ℚ) : ℝ)| + |(((19933793115917 / 5000000000000000) : ℚ) : ℝ)| =
      (((32071079472761 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV10_11RoundedSubstituteRat_error :
    |(manuscriptNormV10_11SubstituteRat : ℝ) - (manuscriptNormV10_11RoundedSubstituteRat : ℝ)| ≤
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((68110340912023 / 10000000000000000) : ℚ) : ℝ)| + |(((7554608004191 / 2500000000000000) : ℚ) : ℝ)| =
      (((98328772928787 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV10_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV10_12RoundedSubstituteRat_error :
    |(manuscriptNormV10_12SubstituteRat : ℝ) - (manuscriptNormV10_12RoundedSubstituteRat : ℝ)| ≤
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2391875533 / 390625000000) : ℚ) : ℝ)| + |(((-8491908331363 / 2000000000000000) : ℚ) : ℝ)| =
      (((20738311060323 / 2000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow10 : ℚ :=
  manuscriptNormV10_0RoundedSubstituteRat +
    manuscriptNormV10_1RoundedSubstituteRat +
    manuscriptNormV10_2RoundedSubstituteRat +
    manuscriptNormV10_3RoundedSubstituteRat +
    manuscriptNormV10_4RoundedSubstituteRat +
    manuscriptNormV10_5RoundedSubstituteRat +
    manuscriptNormV10_6RoundedSubstituteRat +
    manuscriptNormV10_7RoundedSubstituteRat +
    manuscriptNormV10_8RoundedSubstituteRat +
    manuscriptNormV10_9RoundedSubstituteRat +
    manuscriptNormV10_10RoundedSubstituteRat +
    manuscriptNormV10_11RoundedSubstituteRat +
    manuscriptNormV10_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow10_error :
    |(manuscriptNormVSubstituteRow10 : ℝ) - (manuscriptNormVRoundedSubstituteRow10 : ℝ)| ≤
      (((143101652734621 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV10_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV10_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV10_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV10_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV10_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV10_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV10_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV10_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV10_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV10_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV10_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV10_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV10_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow10 manuscriptNormVRoundedSubstituteRow10
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

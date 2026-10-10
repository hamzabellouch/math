import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup021
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup022
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup023
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup024
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup025
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormV5_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV5_0SubstituteRat_interval :
    manuscriptNormV5_0SubstituteRat ∈ Set.Icc manuscriptNormV5_0Interval.1 manuscriptNormV5_0Interval.2 := by
  simpa only [manuscriptNormV5_0SubstituteRat, manuscriptNormV5_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num))

private theorem manuscriptNormV5_0SubstituteRat_upper :
    manuscriptNormV5_0SubstituteRat ≤ (1612117655597126146042737969 / 125000000000000000000000000000) :=
  manuscriptNormV5_0SubstituteRat_interval.2.trans manuscriptNormV5_0_rounded_endpoints.2

def manuscriptNormV5_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV5_1SubstituteRat_interval :
    manuscriptNormV5_1SubstituteRat ∈ Set.Icc manuscriptNormV5_1Interval.1 manuscriptNormV5_1Interval.2 := by
  simpa only [manuscriptNormV5_1SubstituteRat, manuscriptNormV5_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num))

private theorem manuscriptNormV5_1SubstituteRat_upper :
    manuscriptNormV5_1SubstituteRat ≤ (1037754029533411800046178233 / 250000000000000000000000000000) :=
  manuscriptNormV5_1SubstituteRat_interval.2.trans manuscriptNormV5_1_rounded_endpoints.2

def manuscriptNormV5_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV5_2SubstituteRat_interval :
    manuscriptNormV5_2SubstituteRat ∈ Set.Icc manuscriptNormV5_2Interval.1 manuscriptNormV5_2Interval.2 := by
  simpa only [manuscriptNormV5_2SubstituteRat, manuscriptNormV5_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num))

private theorem manuscriptNormV5_2SubstituteRat_upper :
    manuscriptNormV5_2SubstituteRat ≤ (-903158177774137849737278943 / 250000000000000000000000000000) :=
  manuscriptNormV5_2SubstituteRat_interval.2.trans manuscriptNormV5_2_rounded_endpoints.2

def manuscriptNormV5_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV5_3SubstituteRat_interval :
    manuscriptNormV5_3SubstituteRat ∈ Set.Icc manuscriptNormV5_3Interval.1 manuscriptNormV5_3Interval.2 := by
  simpa only [manuscriptNormV5_3SubstituteRat, manuscriptNormV5_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num))

private theorem manuscriptNormV5_3SubstituteRat_upper :
    manuscriptNormV5_3SubstituteRat ≤ (1879305435759342300679999343 / 250000000000000000000000000000) :=
  manuscriptNormV5_3SubstituteRat_interval.2.trans manuscriptNormV5_3_rounded_endpoints.2

def manuscriptNormV5_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV5_4SubstituteRat_interval :
    manuscriptNormV5_4SubstituteRat ∈ Set.Icc manuscriptNormV5_4Interval.1 manuscriptNormV5_4Interval.2 := by
  simpa only [manuscriptNormV5_4SubstituteRat, manuscriptNormV5_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num))

private theorem manuscriptNormV5_4SubstituteRat_upper :
    manuscriptNormV5_4SubstituteRat ≤ (-18285074699575041096073057651 / 1000000000000000000000000000000) :=
  manuscriptNormV5_4SubstituteRat_interval.2.trans manuscriptNormV5_4_rounded_endpoints.2

def manuscriptNormV5_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1)

private theorem manuscriptNormV5_5SubstituteRat_interval :
    manuscriptNormV5_5SubstituteRat ∈ Set.Icc manuscriptNormV5_5Interval.1 manuscriptNormV5_5Interval.2 := by
  simpa only [manuscriptNormV5_5SubstituteRat, manuscriptNormV5_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_5SubstituteRat_upper :
    manuscriptNormV5_5SubstituteRat ≤ (2186983435246917725266771121 / 250000000000000000000000000000) :=
  manuscriptNormV5_5SubstituteRat_interval.2.trans manuscriptNormV5_5_rounded_endpoints.2

def manuscriptNormV5_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1)

private theorem manuscriptNormV5_6SubstituteRat_interval :
    manuscriptNormV5_6SubstituteRat ∈ Set.Icc manuscriptNormV5_6Interval.1 manuscriptNormV5_6Interval.2 := by
  simpa only [manuscriptNormV5_6SubstituteRat, manuscriptNormV5_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_6SubstituteRat_upper :
    manuscriptNormV5_6SubstituteRat ≤ (52036531644412522047429808083 / 1000000000000000000000000000000) :=
  manuscriptNormV5_6SubstituteRat_interval.2.trans manuscriptNormV5_6_rounded_endpoints.2

def manuscriptNormV5_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV5_7SubstituteRat_interval :
    manuscriptNormV5_7SubstituteRat ∈ Set.Icc manuscriptNormV5_7Interval.1 manuscriptNormV5_7Interval.2 := by
  simpa only [manuscriptNormV5_7SubstituteRat, manuscriptNormV5_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_7SubstituteRat_upper :
    manuscriptNormV5_7SubstituteRat ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) :=
  manuscriptNormV5_7SubstituteRat_interval.2.trans manuscriptNormV5_7_rounded_endpoints.2

def manuscriptNormV5_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV5_8SubstituteRat_interval :
    manuscriptNormV5_8SubstituteRat ∈ Set.Icc manuscriptNormV5_8Interval.1 manuscriptNormV5_8Interval.2 := by
  simpa only [manuscriptNormV5_8SubstituteRat, manuscriptNormV5_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_8SubstituteRat_upper :
    manuscriptNormV5_8SubstituteRat ≤ (1161500178636992697332422467 / 125000000000000000000000000000) :=
  manuscriptNormV5_8SubstituteRat_interval.2.trans manuscriptNormV5_8_rounded_endpoints.2

def manuscriptNormV5_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV5_9SubstituteRat_interval :
    manuscriptNormV5_9SubstituteRat ∈ Set.Icc manuscriptNormV5_9Interval.1 manuscriptNormV5_9Interval.2 := by
  simpa only [manuscriptNormV5_9SubstituteRat, manuscriptNormV5_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_9SubstituteRat_upper :
    manuscriptNormV5_9SubstituteRat ≤ (-767346206193196360302151557 / 200000000000000000000000000000) :=
  manuscriptNormV5_9SubstituteRat_interval.2.trans manuscriptNormV5_9_rounded_endpoints.2

def manuscriptNormV5_10SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV5_10SubstituteRat_interval :
    manuscriptNormV5_10SubstituteRat ∈ Set.Icc manuscriptNormV5_10Interval.1 manuscriptNormV5_10Interval.2 := by
  simpa only [manuscriptNormV5_10SubstituteRat, manuscriptNormV5_10Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_10SubstituteRat_upper :
    manuscriptNormV5_10SubstituteRat ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) :=
  manuscriptNormV5_10SubstituteRat_interval.2.trans manuscriptNormV5_10_rounded_endpoints.2

def manuscriptNormV5_11SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV5_11SubstituteRat_interval :
    manuscriptNormV5_11SubstituteRat ∈ Set.Icc manuscriptNormV5_11Interval.1 manuscriptNormV5_11Interval.2 := by
  simpa only [manuscriptNormV5_11SubstituteRat, manuscriptNormV5_11Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_11SubstituteRat_upper :
    manuscriptNormV5_11SubstituteRat ≤ (5545891559125320601256195969 / 500000000000000000000000000000) :=
  manuscriptNormV5_11SubstituteRat_interval.2.trans manuscriptNormV5_11_rounded_endpoints.2

def manuscriptNormV5_12SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV5_12SubstituteRat_interval :
    manuscriptNormV5_12SubstituteRat ∈ Set.Icc manuscriptNormV5_12Interval.1 manuscriptNormV5_12Interval.2 := by
  simpa only [manuscriptNormV5_12SubstituteRat, manuscriptNormV5_12Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))

private theorem manuscriptNormV5_12SubstituteRat_upper :
    manuscriptNormV5_12SubstituteRat ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) :=
  manuscriptNormV5_12SubstituteRat_interval.2.trans manuscriptNormV5_12_rounded_endpoints.2

def manuscriptNormVSubstituteRow5 : ℚ :=
  manuscriptNormV5_0SubstituteRat +
    manuscriptNormV5_1SubstituteRat +
    manuscriptNormV5_2SubstituteRat +
    manuscriptNormV5_3SubstituteRat +
    manuscriptNormV5_4SubstituteRat +
    manuscriptNormV5_5SubstituteRat +
    manuscriptNormV5_6SubstituteRat +
    manuscriptNormV5_7SubstituteRat +
    manuscriptNormV5_8SubstituteRat +
    manuscriptNormV5_9SubstituteRat +
    manuscriptNormV5_10SubstituteRat +
    manuscriptNormV5_11SubstituteRat +
    manuscriptNormV5_12SubstituteRat

theorem manuscriptNormVSubstituteRow5_upper : manuscriptNormVSubstituteRow5 ≤ (117406663890248020465524666789 / 1000000000000000000000000000000) := by
  unfold manuscriptNormVSubstituteRow5
  linarith only [manuscriptNormV5_0SubstituteRat_upper,
    manuscriptNormV5_1SubstituteRat_upper,
    manuscriptNormV5_2SubstituteRat_upper,
    manuscriptNormV5_3SubstituteRat_upper,
    manuscriptNormV5_4SubstituteRat_upper,
    manuscriptNormV5_5SubstituteRat_upper,
    manuscriptNormV5_6SubstituteRat_upper,
    manuscriptNormV5_7SubstituteRat_upper,
    manuscriptNormV5_8SubstituteRat_upper,
    manuscriptNormV5_9SubstituteRat_upper,
    manuscriptNormV5_10SubstituteRat_upper,
    manuscriptNormV5_11SubstituteRat_upper,
    manuscriptNormV5_12SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormV5_0SubstituteRat_composition_error :
    |manuscriptNormV5_0Term - (manuscriptNormV5_0SubstituteRat : ℝ)| ≤ (((1059249365143 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_0SubstituteRat ∈ Set.Icc manuscriptNormV5_0Interval.1 manuscriptNormV5_0Interval.2 := by
    simpa only [manuscriptNormV5_0SubstituteRat, manuscriptNormV5_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_0Interval.1 manuscriptNormV5_0Interval.2 manuscriptNormV5_0SubstituteRat
    (12896941244777008109092538609 / 1000000000000000000000000000000) (1612117655597126146042737969 / 125000000000000000000000000000) manuscriptNormV5_0Term
    manuscriptNormV5_0_exact_interval hq manuscriptNormV5_0_rounded_endpoints.1 manuscriptNormV5_0_rounded_endpoints.2
  have hw : ((1612117655597126146042737969 / 125000000000000000000000000000) - (12896941244777008109092538609 / 1000000000000000000000000000000) : ℚ) = (1059249365143 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_1SubstituteRat_composition_error :
    |manuscriptNormV5_1Term - (manuscriptNormV5_1SubstituteRat : ℝ)| ≤ (((77560278431 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_1SubstituteRat ∈ Set.Icc manuscriptNormV5_1Interval.1 manuscriptNormV5_1Interval.2 := by
    simpa only [manuscriptNormV5_1SubstituteRat, manuscriptNormV5_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_1Interval.1 manuscriptNormV5_1Interval.2 manuscriptNormV5_1SubstituteRat
    (518877014766705861242949901 / 125000000000000000000000000000) (1037754029533411800046178233 / 250000000000000000000000000000) manuscriptNormV5_1Term
    manuscriptNormV5_1_exact_interval hq manuscriptNormV5_1_rounded_endpoints.1 manuscriptNormV5_1_rounded_endpoints.2
  have hw : ((1037754029533411800046178233 / 250000000000000000000000000000) - (518877014766705861242949901 / 125000000000000000000000000000) : ℚ) = (77560278431 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_2SubstituteRat_composition_error :
    |manuscriptNormV5_2Term - (manuscriptNormV5_2SubstituteRat : ℝ)| ≤ (((177391524833 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_2SubstituteRat ∈ Set.Icc manuscriptNormV5_2Interval.1 manuscriptNormV5_2Interval.2 := by
    simpa only [manuscriptNormV5_2SubstituteRat, manuscriptNormV5_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_2Interval.1 manuscriptNormV5_2Interval.2 manuscriptNormV5_2SubstituteRat
    (-722526542219310315268128121 / 200000000000000000000000000000) (-903158177774137849737278943 / 250000000000000000000000000000) manuscriptNormV5_2Term
    manuscriptNormV5_2_exact_interval hq manuscriptNormV5_2_rounded_endpoints.1 manuscriptNormV5_2_rounded_endpoints.2
  have hw : ((-903158177774137849737278943 / 250000000000000000000000000000) - (-722526542219310315268128121 / 200000000000000000000000000000) : ℚ) = (177391524833 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_3SubstituteRat_composition_error :
    |manuscriptNormV5_3Term - (manuscriptNormV5_3SubstituteRat : ℝ)| ≤ (((343760569783 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_3SubstituteRat ∈ Set.Icc manuscriptNormV5_3Interval.1 manuscriptNormV5_3Interval.2 := by
    simpa only [manuscriptNormV5_3SubstituteRat, manuscriptNormV5_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_3Interval.1 manuscriptNormV5_3Interval.2 manuscriptNormV5_3SubstituteRat
    (7517221743037368858959427589 / 1000000000000000000000000000000) (1879305435759342300679999343 / 250000000000000000000000000000) manuscriptNormV5_3Term
    manuscriptNormV5_3_exact_interval hq manuscriptNormV5_3_rounded_endpoints.1 manuscriptNormV5_3_rounded_endpoints.2
  have hw : ((1879305435759342300679999343 / 250000000000000000000000000000) - (7517221743037368858959427589 / 1000000000000000000000000000000) : ℚ) = (343760569783 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_4SubstituteRat_composition_error :
    |manuscriptNormV5_4Term - (manuscriptNormV5_4SubstituteRat : ℝ)| ≤ (((101210232537 / 125000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_4SubstituteRat ∈ Set.Icc manuscriptNormV5_4Interval.1 manuscriptNormV5_4Interval.2 := by
    simpa only [manuscriptNormV5_4SubstituteRat, manuscriptNormV5_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_4Interval.1 manuscriptNormV5_4Interval.2 manuscriptNormV5_4SubstituteRat
    (-18285074699575041905754917947 / 1000000000000000000000000000000) (-18285074699575041096073057651 / 1000000000000000000000000000000) manuscriptNormV5_4Term
    manuscriptNormV5_4_exact_interval hq manuscriptNormV5_4_rounded_endpoints.1 manuscriptNormV5_4_rounded_endpoints.2
  have hw : ((-18285074699575041096073057651 / 1000000000000000000000000000000) - (-18285074699575041905754917947 / 1000000000000000000000000000000) : ℚ) = (101210232537 / 125000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_5SubstituteRat_composition_error :
    |manuscriptNormV5_5Term - (manuscriptNormV5_5SubstituteRat : ℝ)| ≤ (((310739867 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_5SubstituteRat ∈ Set.Icc manuscriptNormV5_5Interval.1 manuscriptNormV5_5Interval.2 := by
    simpa only [manuscriptNormV5_5SubstituteRat, manuscriptNormV5_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_5Interval.1 manuscriptNormV5_5Interval.2 manuscriptNormV5_5SubstituteRat
    (1093491717623458862478015627 / 125000000000000000000000000000) (2186983435246917725266771121 / 250000000000000000000000000000) manuscriptNormV5_5Term
    manuscriptNormV5_5_exact_interval hq manuscriptNormV5_5_rounded_endpoints.1 manuscriptNormV5_5_rounded_endpoints.2
  have hw : ((2186983435246917725266771121 / 250000000000000000000000000000) - (1093491717623458862478015627 / 125000000000000000000000000000) : ℚ) = (310739867 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_6SubstituteRat_composition_error :
    |manuscriptNormV5_6Term - (manuscriptNormV5_6SubstituteRat : ℝ)| ≤ (((140548447 / 12500000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_6SubstituteRat ∈ Set.Icc manuscriptNormV5_6Interval.1 manuscriptNormV5_6Interval.2 := by
    simpa only [manuscriptNormV5_6SubstituteRat, manuscriptNormV5_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_6Interval.1 manuscriptNormV5_6Interval.2 manuscriptNormV5_6SubstituteRat
    (52036531644412522036185932323 / 1000000000000000000000000000000) (52036531644412522047429808083 / 1000000000000000000000000000000) manuscriptNormV5_6Term
    manuscriptNormV5_6_exact_interval hq manuscriptNormV5_6_rounded_endpoints.1 manuscriptNormV5_6_rounded_endpoints.2
  have hw : ((52036531644412522047429808083 / 1000000000000000000000000000000) - (52036531644412522036185932323 / 1000000000000000000000000000000) : ℚ) = (140548447 / 12500000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_7SubstituteRat_composition_error :
    |manuscriptNormV5_7Term - (manuscriptNormV5_7SubstituteRat : ℝ)| ≤ (((3400535907 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_7SubstituteRat ∈ Set.Icc manuscriptNormV5_7Interval.1 manuscriptNormV5_7Interval.2 := by
    simpa only [manuscriptNormV5_7SubstituteRat, manuscriptNormV5_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_7Interval.1 manuscriptNormV5_7Interval.2 manuscriptNormV5_7SubstituteRat
    (2678148258356293550482966351 / 100000000000000000000000000000) (26781482583562935508230199417 / 1000000000000000000000000000000) manuscriptNormV5_7Term
    manuscriptNormV5_7_exact_interval hq manuscriptNormV5_7_rounded_endpoints.1 manuscriptNormV5_7_rounded_endpoints.2
  have hw : ((26781482583562935508230199417 / 1000000000000000000000000000000) - (2678148258356293550482966351 / 100000000000000000000000000000) : ℚ) = (3400535907 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_8SubstituteRat_composition_error :
    |manuscriptNormV5_8Term - (manuscriptNormV5_8SubstituteRat : ℝ)| ≤ (((2073054867 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_8SubstituteRat ∈ Set.Icc manuscriptNormV5_8Interval.1 manuscriptNormV5_8Interval.2 := by
    simpa only [manuscriptNormV5_8SubstituteRat, manuscriptNormV5_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_8Interval.1 manuscriptNormV5_8Interval.2 manuscriptNormV5_8SubstituteRat
    (9292001429095941576586324869 / 1000000000000000000000000000000) (1161500178636992697332422467 / 125000000000000000000000000000) manuscriptNormV5_8Term
    manuscriptNormV5_8_exact_interval hq manuscriptNormV5_8_rounded_endpoints.1 manuscriptNormV5_8_rounded_endpoints.2
  have hw : ((1161500178636992697332422467 / 125000000000000000000000000000) - (9292001429095941576586324869 / 1000000000000000000000000000000) : ℚ) = (2073054867 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_9SubstituteRat_composition_error :
    |manuscriptNormV5_9Term - (manuscriptNormV5_9SubstituteRat : ℝ)| ≤ (((232689437 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_9SubstituteRat ∈ Set.Icc manuscriptNormV5_9Interval.1 manuscriptNormV5_9Interval.2 := by
    simpa only [manuscriptNormV5_9SubstituteRat, manuscriptNormV5_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_9Interval.1 manuscriptNormV5_9Interval.2 manuscriptNormV5_9SubstituteRat
    (-3836731030965981801976136659 / 1000000000000000000000000000000) (-767346206193196360302151557 / 200000000000000000000000000000) manuscriptNormV5_9Term
    manuscriptNormV5_9_exact_interval hq manuscriptNormV5_9_rounded_endpoints.1 manuscriptNormV5_9_rounded_endpoints.2
  have hw : ((-767346206193196360302151557 / 200000000000000000000000000000) - (-3836731030965981801976136659 / 1000000000000000000000000000000) : ℚ) = (232689437 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_10SubstituteRat_composition_error :
    |manuscriptNormV5_10Term - (manuscriptNormV5_10SubstituteRat : ℝ)| ≤ (((2161896379 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_10SubstituteRat ∈ Set.Icc manuscriptNormV5_10Interval.1 manuscriptNormV5_10Interval.2 := by
    simpa only [manuscriptNormV5_10SubstituteRat, manuscriptNormV5_10Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_10Interval.1 manuscriptNormV5_10Interval.2 manuscriptNormV5_10SubstituteRat
    (-2733586989958455530919248339 / 125000000000000000000000000000) (-10934347959833822121515096977 / 500000000000000000000000000000) manuscriptNormV5_10Term
    manuscriptNormV5_10_exact_interval hq manuscriptNormV5_10_rounded_endpoints.1 manuscriptNormV5_10_rounded_endpoints.2
  have hw : ((-10934347959833822121515096977 / 500000000000000000000000000000) - (-2733586989958455530919248339 / 125000000000000000000000000000) : ℚ) = (2161896379 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_11SubstituteRat_composition_error :
    |manuscriptNormV5_11Term - (manuscriptNormV5_11SubstituteRat : ℝ)| ≤ (((1314961523 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_11SubstituteRat ∈ Set.Icc manuscriptNormV5_11Interval.1 manuscriptNormV5_11Interval.2 := by
    simpa only [manuscriptNormV5_11SubstituteRat, manuscriptNormV5_11Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_11Interval.1 manuscriptNormV5_11Interval.2 manuscriptNormV5_11SubstituteRat
    (2218356623650128240239486083 / 200000000000000000000000000000) (5545891559125320601256195969 / 500000000000000000000000000000) manuscriptNormV5_11Term
    manuscriptNormV5_11_exact_interval hq manuscriptNormV5_11_rounded_endpoints.1 manuscriptNormV5_11_rounded_endpoints.2
  have hw : ((5545891559125320601256195969 / 500000000000000000000000000000) - (2218356623650128240239486083 / 200000000000000000000000000000) : ℚ) = (1314961523 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormV5_12SubstituteRat_composition_error :
    |manuscriptNormV5_12Term - (manuscriptNormV5_12SubstituteRat : ℝ)| ≤ (((7520247413 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormV5_12SubstituteRat ∈ Set.Icc manuscriptNormV5_12Interval.1 manuscriptNormV5_12Interval.2 := by
    simpa only [manuscriptNormV5_12SubstituteRat, manuscriptNormV5_12Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormV5_12Interval.1 manuscriptNormV5_12Interval.2 manuscriptNormV5_12SubstituteRat
    (4061860828661937773552758353 / 125000000000000000000000000000) (32494886629295502195942314237 / 1000000000000000000000000000000) manuscriptNormV5_12Term
    manuscriptNormV5_12_exact_interval hq manuscriptNormV5_12_rounded_endpoints.1 manuscriptNormV5_12_rounded_endpoints.2
  have hw : ((32494886629295502195942314237 / 1000000000000000000000000000000) - (4061860828661937773552758353 / 125000000000000000000000000000) : ℚ) = (7520247413 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormVCompositionRow5_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 5 (0, 0)) - (manuscriptNormVSubstituteRow5 : ℝ)| ≤ (((2731909240349 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV5_0SubstituteRat_composition_error
  have h1 := manuscriptNormV5_1SubstituteRat_composition_error
  have h2 := manuscriptNormV5_2SubstituteRat_composition_error
  have h3 := manuscriptNormV5_3SubstituteRat_composition_error
  have h4 := manuscriptNormV5_4SubstituteRat_composition_error
  have h5 := manuscriptNormV5_5SubstituteRat_composition_error
  have h6 := manuscriptNormV5_6SubstituteRat_composition_error
  have h7 := manuscriptNormV5_7SubstituteRat_composition_error
  have h8 := manuscriptNormV5_8SubstituteRat_composition_error
  have h9 := manuscriptNormV5_9SubstituteRat_composition_error
  have h10 := manuscriptNormV5_10SubstituteRat_composition_error
  have h11 := manuscriptNormV5_11SubstituteRat_composition_error
  have h12 := manuscriptNormV5_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV5_0Term + (manuscriptNormV5_1Term + (manuscriptNormV5_2Term + (manuscriptNormV5_3Term + (manuscriptNormV5_4Term + (manuscriptNormV5_5Term + (manuscriptNormV5_6Term + (manuscriptNormV5_7Term + (manuscriptNormV5_8Term + (manuscriptNormV5_9Term + (manuscriptNormV5_10Term + (manuscriptNormV5_11Term + (manuscriptNormV5_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow5 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow5
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

def manuscriptNormV5_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV5_0RoundedSubstituteRat_error :
    |(manuscriptNormV5_0SubstituteRat : ℝ) - (manuscriptNormV5_0RoundedSubstituteRat : ℝ)| ≤
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203) (by norm_num) (by norm_num)
  have hw : |(((-207003480727327 / 10000000000000000) : ℚ) : ℝ)| + |(((-9130910809039 / 312500000000000) : ℚ) : ℝ)| =
      (((19967705064663 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV5_1RoundedSubstituteRat_error :
    |(manuscriptNormV5_1SubstituteRat : ℝ) - (manuscriptNormV5_1RoundedSubstituteRat : ℝ)| ≤
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093) (by norm_num) (by norm_num)
  have hw : |(((-30314387010667 / 5000000000000000) : ℚ) : ℝ)| + |(((-1337165747419 / 156250000000000) : ℚ) : ℝ)| =
      (((2924147637123 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527)

private theorem manuscriptNormV5_2RoundedSubstituteRat_error :
    |(manuscriptNormV5_2SubstituteRat : ℝ) - (manuscriptNormV5_2RoundedSubstituteRat : ℝ)| ≤
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-17333342034543 / 5000000000000000) (-764572651551 / 156250000000000) (0) (-1) (574666 / 390625) (98 / 527) (by norm_num) (by norm_num)
  have hw : |(((-17333342034543 / 5000000000000000) : ℚ) : ℝ)| + |(((-764572651551 / 156250000000000) : ℚ) : ℝ)| =
      (((1671986675367 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741)

private theorem manuscriptNormV5_3RoundedSubstituteRat_error :
    |(manuscriptNormV5_3SubstituteRat : ℝ) - (manuscriptNormV5_3RoundedSubstituteRat : ℝ)| ≤
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (33589651698169 / 5000000000000000) (1481637471433 / 156250000000000) (0) (-1) (1549081 / 1000000) (259 / 1741) (by norm_num) (by norm_num)
  have hw : |(((33589651698169 / 5000000000000000) : ℚ) : ℝ)| + |(((1481637471433 / 156250000000000) : ℚ) : ℝ)| =
      (((3240082031361 / 200000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047)

private theorem manuscriptNormV5_4RoundedSubstituteRat_error :
    |(manuscriptNormV5_4SubstituteRat : ℝ) - (manuscriptNormV5_4RoundedSubstituteRat : ℝ)| ≤
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-158231827865049 / 10000000000000000) (-6979596199593 / 312500000000000) (0) (-1) (62073709 / 39062500) (1453 / 11047) (by norm_num) (by norm_num)
  have hw : |(((-158231827865049 / 10000000000000000) : ℚ) : ℝ)| + |(((-6979596199593 / 312500000000000) : ℚ) : ℝ)| =
      (((15263156250081 / 400000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1)

private theorem manuscriptNormV5_5RoundedSubstituteRat_error :
    |(manuscriptNormV5_5SubstituteRat : ℝ) - (manuscriptNormV5_5RoundedSubstituteRat : ℝ)| ≤
      (((707710226868727 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7362962422863 / 400000000000000) (-8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((7362962422863 / 400000000000000) : ℚ) : ℝ)| + |(((-8181815098393 / 156250000000000) : ℚ) : ℝ)| =
      (((707710226868727 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1)

private theorem manuscriptNormV5_6RoundedSubstituteRat_error :
    |(manuscriptNormV5_6SubstituteRat : ℝ) - (manuscriptNormV5_6RoundedSubstituteRat : ℝ)| ≤
      (((555047830758473 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-555047830758473 / 10000000000000000) (0 / 1) (-3) (0) (958441 / 781250) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-555047830758473 / 10000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((555047830758473 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV5_7RoundedSubstituteRat_error :
    |(manuscriptNormV5_7SubstituteRat : ℝ) - (manuscriptNormV5_7RoundedSubstituteRat : ℝ)| ≤
      (((599270904878273 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((251798416946459 / 5000000000000000) : ℚ) : ℝ)| + |(((19134814197071 / 2000000000000000) : ℚ) : ℝ)| =
      (((599270904878273 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV5_8RoundedSubstituteRat_error :
    |(manuscriptNormV5_8SubstituteRat : ℝ) - (manuscriptNormV5_8RoundedSubstituteRat : ℝ)| ≤
      (((583577347045887 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-7675142212993 / 1000000000000000) : ℚ) : ℝ)| + |(((506825924915957 / 10000000000000000) : ℚ) : ℝ)| =
      (((583577347045887 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV5_9RoundedSubstituteRat_error :
    |(manuscriptNormV5_9SubstituteRat : ℝ) - (manuscriptNormV5_9RoundedSubstituteRat : ℝ)| ≤
      (((53594091090839 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-68919525805689 / 10000000000000000) : ℚ) : ℝ)| + |(((145456838557667 / 10000000000000000) : ℚ) : ℝ)| =
      (((53594091090839 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_10RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV5_10RoundedSubstituteRat_error :
    |(manuscriptNormV5_10SubstituteRat : ℝ) - (manuscriptNormV5_10RoundedSubstituteRat : ℝ)| ≤
      (((88430832620597 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((160081263898183 / 10000000000000000) : ℚ) : ℝ)| + |(((-16780401343011 / 10000000000000000) : ℚ) : ℝ)| =
      (((88430832620597 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV5_11RoundedSubstituteRat_error :
    |(manuscriptNormV5_11SubstituteRat : ℝ) - (manuscriptNormV5_11RoundedSubstituteRat : ℝ)| ≤
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((389474106710791 / 20000000000000000) : ℚ) : ℝ)| + |(((-335265249034277 / 20000000000000000) : ℚ) : ℝ)| =
      (((181184838936267 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormV5_12RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV5_12RoundedSubstituteRat_error :
    |(manuscriptNormV5_12SubstituteRat : ℝ) - (manuscriptNormV5_12RoundedSubstituteRat : ℝ)| ≤
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-445455465826873 / 20000000000000000) : ℚ) : ℝ)| + |(((256246551143909 / 20000000000000000) : ℚ) : ℝ)| =
      (((350851008485391 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormVRoundedSubstituteRow5 : ℚ :=
  manuscriptNormV5_0RoundedSubstituteRat +
    manuscriptNormV5_1RoundedSubstituteRat +
    manuscriptNormV5_2RoundedSubstituteRat +
    manuscriptNormV5_3RoundedSubstituteRat +
    manuscriptNormV5_4RoundedSubstituteRat +
    manuscriptNormV5_5RoundedSubstituteRat +
    manuscriptNormV5_6RoundedSubstituteRat +
    manuscriptNormV5_7RoundedSubstituteRat +
    manuscriptNormV5_8RoundedSubstituteRat +
    manuscriptNormV5_9RoundedSubstituteRat +
    manuscriptNormV5_10RoundedSubstituteRat +
    manuscriptNormV5_11RoundedSubstituteRat +
    manuscriptNormV5_12RoundedSubstituteRat

theorem manuscriptNormVRoundedRow5_error :
    |(manuscriptNormVSubstituteRow5 : ℝ) - (manuscriptNormVRoundedSubstituteRow5 : ℝ)| ≤
      (((964529475114997 / 2000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormV5_0RoundedSubstituteRat_error
  have h1 := manuscriptNormV5_1RoundedSubstituteRat_error
  have h2 := manuscriptNormV5_2RoundedSubstituteRat_error
  have h3 := manuscriptNormV5_3RoundedSubstituteRat_error
  have h4 := manuscriptNormV5_4RoundedSubstituteRat_error
  have h5 := manuscriptNormV5_5RoundedSubstituteRat_error
  have h6 := manuscriptNormV5_6RoundedSubstituteRat_error
  have h7 := manuscriptNormV5_7RoundedSubstituteRat_error
  have h8 := manuscriptNormV5_8RoundedSubstituteRat_error
  have h9 := manuscriptNormV5_9RoundedSubstituteRat_error
  have h10 := manuscriptNormV5_10RoundedSubstituteRat_error
  have h11 := manuscriptNormV5_11RoundedSubstituteRat_error
  have h12 := manuscriptNormV5_12RoundedSubstituteRat_error
  unfold manuscriptNormVSubstituteRow5 manuscriptNormVRoundedSubstituteRow5
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

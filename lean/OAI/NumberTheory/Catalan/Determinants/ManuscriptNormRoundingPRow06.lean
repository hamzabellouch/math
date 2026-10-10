import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup019
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup020
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup021
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup022
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP6_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP6_0SubstituteRat_interval :
    manuscriptNormP6_0SubstituteRat ∈ Set.Icc manuscriptNormP6_0Interval.1 manuscriptNormP6_0Interval.2 := by
  simpa only [manuscriptNormP6_0SubstituteRat, manuscriptNormP6_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num))

private theorem manuscriptNormP6_0SubstituteRat_upper :
    manuscriptNormP6_0SubstituteRat ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) :=
  manuscriptNormP6_0SubstituteRat_interval.2.trans manuscriptNormP6_0_rounded_endpoints.2

def manuscriptNormP6_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP6_1SubstituteRat_interval :
    manuscriptNormP6_1SubstituteRat ∈ Set.Icc manuscriptNormP6_1Interval.1 manuscriptNormP6_1Interval.2 := by
  simpa only [manuscriptNormP6_1SubstituteRat, manuscriptNormP6_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num))

private theorem manuscriptNormP6_1SubstituteRat_upper :
    manuscriptNormP6_1SubstituteRat ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) :=
  manuscriptNormP6_1SubstituteRat_interval.2.trans manuscriptNormP6_1_rounded_endpoints.2

def manuscriptNormP6_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP6_2SubstituteRat_interval :
    manuscriptNormP6_2SubstituteRat ∈ Set.Icc manuscriptNormP6_2Interval.1 manuscriptNormP6_2Interval.2 := by
  simpa only [manuscriptNormP6_2SubstituteRat, manuscriptNormP6_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num))

private theorem manuscriptNormP6_2SubstituteRat_upper :
    manuscriptNormP6_2SubstituteRat ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) :=
  manuscriptNormP6_2SubstituteRat_interval.2.trans manuscriptNormP6_2_rounded_endpoints.2

def manuscriptNormP6_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP6_3SubstituteRat_interval :
    manuscriptNormP6_3SubstituteRat ∈ Set.Icc manuscriptNormP6_3Interval.1 manuscriptNormP6_3Interval.2 := by
  simpa only [manuscriptNormP6_3SubstituteRat, manuscriptNormP6_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num))

private theorem manuscriptNormP6_3SubstituteRat_upper :
    manuscriptNormP6_3SubstituteRat ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) :=
  manuscriptNormP6_3SubstituteRat_interval.2.trans manuscriptNormP6_3_rounded_endpoints.2

def manuscriptNormP6_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP6_4SubstituteRat_interval :
    manuscriptNormP6_4SubstituteRat ∈ Set.Icc manuscriptNormP6_4Interval.1 manuscriptNormP6_4Interval.2 := by
  simpa only [manuscriptNormP6_4SubstituteRat, manuscriptNormP6_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))

private theorem manuscriptNormP6_4SubstituteRat_upper :
    manuscriptNormP6_4SubstituteRat ≤ (1095337454857858872694069 / 1600000000000000000000000000) :=
  manuscriptNormP6_4SubstituteRat_interval.2.trans manuscriptNormP6_4_rounded_endpoints.2

def manuscriptNormP6_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP6_5SubstituteRat_interval :
    manuscriptNormP6_5SubstituteRat ∈ Set.Icc manuscriptNormP6_5Interval.1 manuscriptNormP6_5Interval.2 := by
  simpa only [manuscriptNormP6_5SubstituteRat, manuscriptNormP6_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))

private theorem manuscriptNormP6_5SubstituteRat_upper :
    manuscriptNormP6_5SubstituteRat ≤ (1016528929435293007022945239 / 500000000000000000000000000000) :=
  manuscriptNormP6_5SubstituteRat_interval.2.trans manuscriptNormP6_5_rounded_endpoints.2

def manuscriptNormP6_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871)

private theorem manuscriptNormP6_6SubstituteRat_interval :
    manuscriptNormP6_6SubstituteRat ∈ Set.Icc manuscriptNormP6_6Interval.1 manuscriptNormP6_6Interval.2 := by
  simpa only [manuscriptNormP6_6SubstituteRat, manuscriptNormP6_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871) (by norm_num))

private theorem manuscriptNormP6_6SubstituteRat_upper :
    manuscriptNormP6_6SubstituteRat ≤ (929632514821460500962879519 / 1000000000000000000000000000000) :=
  manuscriptNormP6_6SubstituteRat_interval.2.trans manuscriptNormP6_6_rounded_endpoints.2

def manuscriptNormP6_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP6_7SubstituteRat_interval :
    manuscriptNormP6_7SubstituteRat ∈ Set.Icc manuscriptNormP6_7Interval.1 manuscriptNormP6_7Interval.2 := by
  simpa only [manuscriptNormP6_7SubstituteRat, manuscriptNormP6_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormP6_7SubstituteRat_upper :
    manuscriptNormP6_7SubstituteRat ≤ (4348474977237654107423445337 / 1000000000000000000000000000000) :=
  manuscriptNormP6_7SubstituteRat_interval.2.trans manuscriptNormP6_7_rounded_endpoints.2

def manuscriptNormP6_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP6_8SubstituteRat_interval :
    manuscriptNormP6_8SubstituteRat ∈ Set.Icc manuscriptNormP6_8Interval.1 manuscriptNormP6_8Interval.2 := by
  simpa only [manuscriptNormP6_8SubstituteRat, manuscriptNormP6_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num))

private theorem manuscriptNormP6_8SubstituteRat_upper :
    manuscriptNormP6_8SubstituteRat ≤ (-271717843418425718753445767 / 200000000000000000000000000000) :=
  manuscriptNormP6_8SubstituteRat_interval.2.trans manuscriptNormP6_8_rounded_endpoints.2

def manuscriptNormP6_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709)

private theorem manuscriptNormP6_9SubstituteRat_interval :
    manuscriptNormP6_9SubstituteRat ∈ Set.Icc manuscriptNormP6_9Interval.1 manuscriptNormP6_9Interval.2 := by
  simpa only [manuscriptNormP6_9SubstituteRat, manuscriptNormP6_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709) (by norm_num))

private theorem manuscriptNormP6_9SubstituteRat_upper :
    manuscriptNormP6_9SubstituteRat ≤ (-345347922628817831427739889 / 200000000000000000000000000000) :=
  manuscriptNormP6_9SubstituteRat_interval.2.trans manuscriptNormP6_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow6 : ℚ :=
  manuscriptNormP6_0SubstituteRat +
    manuscriptNormP6_1SubstituteRat +
    manuscriptNormP6_2SubstituteRat +
    manuscriptNormP6_3SubstituteRat +
    manuscriptNormP6_4SubstituteRat +
    manuscriptNormP6_5SubstituteRat +
    manuscriptNormP6_6SubstituteRat +
    manuscriptNormP6_7SubstituteRat +
    manuscriptNormP6_8SubstituteRat +
    manuscriptNormP6_9SubstituteRat

theorem manuscriptNormPSubstituteRow6_upper : manuscriptNormPSubstituteRow6 ≤ (-281018627847640469871664967 / 62500000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow6
  linarith only [manuscriptNormP6_0SubstituteRat_upper,
    manuscriptNormP6_1SubstituteRat_upper,
    manuscriptNormP6_2SubstituteRat_upper,
    manuscriptNormP6_3SubstituteRat_upper,
    manuscriptNormP6_4SubstituteRat_upper,
    manuscriptNormP6_5SubstituteRat_upper,
    manuscriptNormP6_6SubstituteRat_upper,
    manuscriptNormP6_7SubstituteRat_upper,
    manuscriptNormP6_8SubstituteRat_upper,
    manuscriptNormP6_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP6_0SubstituteRat_composition_error :
    |manuscriptNormP6_0Term - (manuscriptNormP6_0SubstituteRat : ℝ)| ≤ (((75563940457 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_0SubstituteRat ∈ Set.Icc manuscriptNormP6_0Interval.1 manuscriptNormP6_0Interval.2 := by
    simpa only [manuscriptNormP6_0SubstituteRat, manuscriptNormP6_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_0Interval.1 manuscriptNormP6_0Interval.2 manuscriptNormP6_0SubstituteRat
    (-160926007121511347938212133 / 50000000000000000000000000000) (-1609260071215113403818180873 / 500000000000000000000000000000) manuscriptNormP6_0Term
    manuscriptNormP6_0_exact_interval hq manuscriptNormP6_0_rounded_endpoints.1 manuscriptNormP6_0_rounded_endpoints.2
  have hw : ((-1609260071215113403818180873 / 500000000000000000000000000000) - (-160926007121511347938212133 / 50000000000000000000000000000) : ℚ) = (75563940457 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_1SubstituteRat_composition_error :
    |manuscriptNormP6_1Term - (manuscriptNormP6_1SubstituteRat : ℝ)| ≤ (((34656891447 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_1SubstituteRat ∈ Set.Icc manuscriptNormP6_1Interval.1 manuscriptNormP6_1Interval.2 := by
    simpa only [manuscriptNormP6_1SubstituteRat, manuscriptNormP6_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_1Interval.1 manuscriptNormP6_1Interval.2 manuscriptNormP6_1SubstituteRat
    (-200978735801924450580405149 / 250000000000000000000000000000) (-803914943207697767664729149 / 1000000000000000000000000000000) manuscriptNormP6_1Term
    manuscriptNormP6_1_exact_interval hq manuscriptNormP6_1_rounded_endpoints.1 manuscriptNormP6_1_rounded_endpoints.2
  have hw : ((-803914943207697767664729149 / 1000000000000000000000000000000) - (-200978735801924450580405149 / 250000000000000000000000000000) : ℚ) = (34656891447 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_2SubstituteRat_composition_error :
    |manuscriptNormP6_2Term - (manuscriptNormP6_2SubstituteRat : ℝ)| ≤ (((21046071 / 25000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_2SubstituteRat ∈ Set.Icc manuscriptNormP6_2Interval.1 manuscriptNormP6_2Interval.2 := by
    simpa only [manuscriptNormP6_2SubstituteRat, manuscriptNormP6_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_2Interval.1 manuscriptNormP6_2Interval.2 manuscriptNormP6_2SubstituteRat
    (-6685833039281012505245132349 / 1000000000000000000000000000000) (-6685833039281012504403289509 / 1000000000000000000000000000000) manuscriptNormP6_2Term
    manuscriptNormP6_2_exact_interval hq manuscriptNormP6_2_rounded_endpoints.1 manuscriptNormP6_2_rounded_endpoints.2
  have hw : ((-6685833039281012504403289509 / 1000000000000000000000000000000) - (-6685833039281012505245132349 / 1000000000000000000000000000000) : ℚ) = (21046071 / 25000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_3SubstituteRat_composition_error :
    |manuscriptNormP6_3Term - (manuscriptNormP6_3SubstituteRat : ℝ)| ≤ (((179965263 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_3SubstituteRat ∈ Set.Icc manuscriptNormP6_3Interval.1 manuscriptNormP6_3Interval.2 := by
    simpa only [manuscriptNormP6_3SubstituteRat, manuscriptNormP6_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_3Interval.1 manuscriptNormP6_3Interval.2 manuscriptNormP6_3SubstituteRat
    (1301547649377044894437730227 / 1000000000000000000000000000000) (1301547649377044894797660753 / 1000000000000000000000000000000) manuscriptNormP6_3Term
    manuscriptNormP6_3_exact_interval hq manuscriptNormP6_3_rounded_endpoints.1 manuscriptNormP6_3_rounded_endpoints.2
  have hw : ((1301547649377044894797660753 / 1000000000000000000000000000000) - (1301547649377044894437730227 / 1000000000000000000000000000000) : ℚ) = (179965263 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_4SubstituteRat_composition_error :
    |manuscriptNormP6_4Term - (manuscriptNormP6_4SubstituteRat : ℝ)| ≤ (((8376447 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_4SubstituteRat ∈ Set.Icc manuscriptNormP6_4Interval.1 manuscriptNormP6_4Interval.2 := by
    simpa only [manuscriptNormP6_4SubstituteRat, manuscriptNormP6_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_4Interval.1 manuscriptNormP6_4Interval.2 manuscriptNormP6_4SubstituteRat
    (136917181857232359070005731 / 200000000000000000000000000000) (1095337454857858872694069 / 1600000000000000000000000000) manuscriptNormP6_4Term
    manuscriptNormP6_4_exact_interval hq manuscriptNormP6_4_rounded_endpoints.1 manuscriptNormP6_4_rounded_endpoints.2
  have hw : ((1095337454857858872694069 / 1600000000000000000000000000) - (136917181857232359070005731 / 200000000000000000000000000000) : ℚ) = (8376447 / 100000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_5SubstituteRat_composition_error :
    |manuscriptNormP6_5Term - (manuscriptNormP6_5SubstituteRat : ℝ)| ≤ (((97182271 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_5SubstituteRat ∈ Set.Icc manuscriptNormP6_5Interval.1 manuscriptNormP6_5Interval.2 := by
    simpa only [manuscriptNormP6_5SubstituteRat, manuscriptNormP6_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_5Interval.1 manuscriptNormP6_5Interval.2 manuscriptNormP6_5SubstituteRat
    (2033057858870586013559979123 / 1000000000000000000000000000000) (1016528929435293007022945239 / 500000000000000000000000000000) manuscriptNormP6_5Term
    manuscriptNormP6_5_exact_interval hq manuscriptNormP6_5_rounded_endpoints.1 manuscriptNormP6_5_rounded_endpoints.2
  have hw : ((1016528929435293007022945239 / 500000000000000000000000000000) - (2033057858870586013559979123 / 1000000000000000000000000000000) : ℚ) = (97182271 / 200000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_6SubstituteRat_composition_error :
    |manuscriptNormP6_6Term - (manuscriptNormP6_6SubstituteRat : ℝ)| ≤ (((117010141 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_6SubstituteRat ∈ Set.Icc manuscriptNormP6_6Interval.1 manuscriptNormP6_6Interval.2 := by
    simpa only [manuscriptNormP6_6SubstituteRat, manuscriptNormP6_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_6Interval.1 manuscriptNormP6_6Interval.2 manuscriptNormP6_6SubstituteRat
    (464816257410730250422934689 / 500000000000000000000000000000) (929632514821460500962879519 / 1000000000000000000000000000000) manuscriptNormP6_6Term
    manuscriptNormP6_6_exact_interval hq manuscriptNormP6_6_rounded_endpoints.1 manuscriptNormP6_6_rounded_endpoints.2
  have hw : ((929632514821460500962879519 / 1000000000000000000000000000000) - (464816257410730250422934689 / 500000000000000000000000000000) : ℚ) = (117010141 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_7SubstituteRat_composition_error :
    |manuscriptNormP6_7Term - (manuscriptNormP6_7SubstituteRat : ℝ)| ≤ (((228200393 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_7SubstituteRat ∈ Set.Icc manuscriptNormP6_7Interval.1 manuscriptNormP6_7Interval.2 := by
    simpa only [manuscriptNormP6_7SubstituteRat, manuscriptNormP6_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_7Interval.1 manuscriptNormP6_7Interval.2 manuscriptNormP6_7SubstituteRat
    (869694995447530821302128753 / 200000000000000000000000000000) (4348474977237654107423445337 / 1000000000000000000000000000000) manuscriptNormP6_7Term
    manuscriptNormP6_7_exact_interval hq manuscriptNormP6_7_rounded_endpoints.1 manuscriptNormP6_7_rounded_endpoints.2
  have hw : ((4348474977237654107423445337 / 1000000000000000000000000000000) - (869694995447530821302128753 / 200000000000000000000000000000) : ℚ) = (228200393 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_8SubstituteRat_composition_error :
    |manuscriptNormP6_8Term - (manuscriptNormP6_8SubstituteRat : ℝ)| ≤ (((148518127 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_8SubstituteRat ∈ Set.Icc manuscriptNormP6_8Interval.1 manuscriptNormP6_8Interval.2 := by
    simpa only [manuscriptNormP6_8SubstituteRat, manuscriptNormP6_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_8Interval.1 manuscriptNormP6_8Interval.2 manuscriptNormP6_8SubstituteRat
    (-679294608546064296957873481 / 500000000000000000000000000000) (-271717843418425718753445767 / 200000000000000000000000000000) manuscriptNormP6_8Term
    manuscriptNormP6_8_exact_interval hq manuscriptNormP6_8_rounded_endpoints.1 manuscriptNormP6_8_rounded_endpoints.2
  have hw : ((-271717843418425718753445767 / 200000000000000000000000000000) - (-679294608546064296957873481 / 500000000000000000000000000000) : ℚ) = (148518127 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP6_9SubstituteRat_composition_error :
    |manuscriptNormP6_9Term - (manuscriptNormP6_9SubstituteRat : ℝ)| ≤ (((22122556297 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP6_9SubstituteRat ∈ Set.Icc manuscriptNormP6_9Interval.1 manuscriptNormP6_9Interval.2 := by
    simpa only [manuscriptNormP6_9SubstituteRat, manuscriptNormP6_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP6_9Interval.1 manuscriptNormP6_9Interval.2 manuscriptNormP6_9SubstituteRat
    (-1726739613144089201383812039 / 1000000000000000000000000000000) (-345347922628817831427739889 / 200000000000000000000000000000) manuscriptNormP6_9Term
    manuscriptNormP6_9_exact_interval hq manuscriptNormP6_9_rounded_endpoints.1 manuscriptNormP6_9_rounded_endpoints.2
  have hw : ((-345347922628817831427739889 / 200000000000000000000000000000) - (-1726739613144089201383812039 / 1000000000000000000000000000000) : ℚ) = (22122556297 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow6_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 6 (0, 0)) - (manuscriptNormPSubstituteRow6 : ℝ)| ≤ (((116489831993 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP6_0SubstituteRat_composition_error
  have h1 := manuscriptNormP6_1SubstituteRat_composition_error
  have h2 := manuscriptNormP6_2SubstituteRat_composition_error
  have h3 := manuscriptNormP6_3SubstituteRat_composition_error
  have h4 := manuscriptNormP6_4SubstituteRat_composition_error
  have h5 := manuscriptNormP6_5SubstituteRat_composition_error
  have h6 := manuscriptNormP6_6SubstituteRat_composition_error
  have h7 := manuscriptNormP6_7SubstituteRat_composition_error
  have h8 := manuscriptNormP6_8SubstituteRat_composition_error
  have h9 := manuscriptNormP6_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP6_0Term + (manuscriptNormP6_1Term + (manuscriptNormP6_2Term + (manuscriptNormP6_3Term + (manuscriptNormP6_4Term + (manuscriptNormP6_5Term + (manuscriptNormP6_6Term + (manuscriptNormP6_7Term + (manuscriptNormP6_8Term + (manuscriptNormP6_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow6 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow6
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

def manuscriptNormP6_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP6_0RoundedSubstituteRat_error :
    |(manuscriptNormP6_0SubstituteRat : ℝ) - (manuscriptNormP6_0RoundedSubstituteRat : ℝ)| ≤
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519) (by norm_num) (by norm_num)
  have hw : |(((-3765635049867 / 2500000000000000) : ℚ) : ℝ)| + |(((-10421985581721 / 2500000000000000) : ℚ) : ℝ)| =
      (((3546905157897 / 625000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP6_1RoundedSubstituteRat_error :
    |(manuscriptNormP6_1SubstituteRat : ℝ) - (manuscriptNormP6_1RoundedSubstituteRat : ℝ)| ≤
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229) (by norm_num) (by norm_num)
  have hw : |(((-3454166215131 / 10000000000000000) : ℚ) : ℝ)| + |(((-9559946732553 / 10000000000000000) : ℚ) : ℝ)| =
      (((3253528236921 / 2500000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP6_2RoundedSubstituteRat_error :
    |(manuscriptNormP6_2SubstituteRat : ℝ) - (manuscriptNormP6_2RoundedSubstituteRat : ℝ)| ≤
      (((246874744865487 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110) (by norm_num) (by norm_num)
  have hw : |(((-249342691992771 / 20000000000000000) : ℚ) : ℝ)| + |(((-244406797738203 / 20000000000000000) : ℚ) : ℝ)| =
      (((246874744865487 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP6_3RoundedSubstituteRat_error :
    |(manuscriptNormP6_3SubstituteRat : ℝ) - (manuscriptNormP6_3RoundedSubstituteRat : ℝ)| ≤
      (((1196479841631 / 62500000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890) (by norm_num) (by norm_num)
  have hw : |(((284284403283 / 160000000000000) : ℚ) : ℝ)| + |(((-69467599782309 / 4000000000000000) : ℚ) : ℝ)| =
      (((1196479841631 / 62500000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP6_4RoundedSubstituteRat_error :
    |(manuscriptNormP6_4SubstituteRat : ℝ) - (manuscriptNormP6_4RoundedSubstituteRat : ℝ)| ≤
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((6202476756039 / 5000000000000000) : ℚ) : ℝ)| + |(((-7590127221861 / 10000000000000000) : ℚ) : ℝ)| =
      (((19995080733939 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP6_5RoundedSubstituteRat_error :
    |(manuscriptNormP6_5SubstituteRat : ℝ) - (manuscriptNormP6_5RoundedSubstituteRat : ℝ)| ≤
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090) (by norm_num) (by norm_num)
  have hw : |(((-14391556077387 / 10000000000000000) : ℚ) : ℝ)| + |(((1045946527347 / 5000000000000000) : ℚ) : ℝ)| =
      (((16483449132081 / 10000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871)

private theorem manuscriptNormP6_6RoundedSubstituteRat_error :
    |(manuscriptNormP6_6SubstituteRat : ℝ) - (manuscriptNormP6_6RoundedSubstituteRat : ℝ)| ≤
      (((15863789619207 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871) (by norm_num) (by norm_num)
  have hw : |(((2165837981751 / 1250000000000000) : ℚ) : ℝ)| + |(((-7200437692203 / 5000000000000000) : ℚ) : ℝ)| =
      (((15863789619207 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP6_7RoundedSubstituteRat_error :
    |(manuscriptNormP6_7SubstituteRat : ℝ) - (manuscriptNormP6_7RoundedSubstituteRat : ℝ)| ≤
      (((2252997732537 / 1000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-2252997732537 / 1000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((2252997732537 / 1000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP6_8RoundedSubstituteRat_error :
    |(manuscriptNormP6_8SubstituteRat : ℝ) - (manuscriptNormP6_8RoundedSubstituteRat : ℝ)| ≤
      (((12311306556531 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-43980712089603 / 20000000000000000) : ℚ) : ℝ)| + |(((5264514136521 / 20000000000000000) : ℚ) : ℝ)| =
      (((12311306556531 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP6_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709)

private theorem manuscriptNormP6_9RoundedSubstituteRat_error :
    |(manuscriptNormP6_9SubstituteRat : ℝ) - (manuscriptNormP6_9RoundedSubstituteRat : ℝ)| ≤
      (((24500663139 / 8000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709) (by norm_num) (by norm_num)
  have hw : |(((7437685121511 / 4000000000000000) : ℚ) : ℝ)| + |(((-4812646447989 / 4000000000000000) : ℚ) : ℝ)| =
      (((24500663139 / 8000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow6 : ℚ :=
  manuscriptNormP6_0RoundedSubstituteRat +
    manuscriptNormP6_1RoundedSubstituteRat +
    manuscriptNormP6_2RoundedSubstituteRat +
    manuscriptNormP6_3RoundedSubstituteRat +
    manuscriptNormP6_4RoundedSubstituteRat +
    manuscriptNormP6_5RoundedSubstituteRat +
    manuscriptNormP6_6RoundedSubstituteRat +
    manuscriptNormP6_7RoundedSubstituteRat +
    manuscriptNormP6_8RoundedSubstituteRat +
    manuscriptNormP6_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow6_error :
    |(manuscriptNormPSubstituteRow6 : ℝ) - (manuscriptNormPRoundedSubstituteRow6 : ℝ)| ≤
      (((654060643467099 / 10000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP6_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP6_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP6_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP6_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP6_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP6_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP6_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP6_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP6_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP6_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow6 manuscriptNormPRoundedSubstituteRow6
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

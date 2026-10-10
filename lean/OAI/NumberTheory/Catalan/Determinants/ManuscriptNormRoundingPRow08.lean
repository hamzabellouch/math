import Mathlib.Tactic.Linarith
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup026
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup027
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup028
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup029
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

namespace InternalCatalan
open scoped BigOperators

def manuscriptNormP8_0SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP8_0SubstituteRat_interval :
    manuscriptNormP8_0SubstituteRat ∈ Set.Icc manuscriptNormP8_0Interval.1 manuscriptNormP8_0Interval.2 := by
  simpa only [manuscriptNormP8_0SubstituteRat, manuscriptNormP8_0Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num))

private theorem manuscriptNormP8_0SubstituteRat_upper :
    manuscriptNormP8_0SubstituteRat ≤ (476374564998450126700803411 / 200000000000000000000000000000) :=
  manuscriptNormP8_0SubstituteRat_interval.2.trans manuscriptNormP8_0_rounded_endpoints.2

def manuscriptNormP8_1SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP8_1SubstituteRat_interval :
    manuscriptNormP8_1SubstituteRat ∈ Set.Icc manuscriptNormP8_1Interval.1 manuscriptNormP8_1Interval.2 := by
  simpa only [manuscriptNormP8_1SubstituteRat, manuscriptNormP8_1Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num))

private theorem manuscriptNormP8_1SubstituteRat_upper :
    manuscriptNormP8_1SubstituteRat ≤ (580408182566126009652303041 / 1000000000000000000000000000000) :=
  manuscriptNormP8_1SubstituteRat_interval.2.trans manuscriptNormP8_1_rounded_endpoints.2

def manuscriptNormP8_2SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP8_2SubstituteRat_interval :
    manuscriptNormP8_2SubstituteRat ∈ Set.Icc manuscriptNormP8_2Interval.1 manuscriptNormP8_2Interval.2 := by
  simpa only [manuscriptNormP8_2SubstituteRat, manuscriptNormP8_2Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num))

private theorem manuscriptNormP8_2SubstituteRat_upper :
    manuscriptNormP8_2SubstituteRat ≤ (121817418346790177253223493 / 100000000000000000000000000000) :=
  manuscriptNormP8_2SubstituteRat_interval.2.trans manuscriptNormP8_2_rounded_endpoints.2

def manuscriptNormP8_3SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP8_3SubstituteRat_interval :
    manuscriptNormP8_3SubstituteRat ∈ Set.Icc manuscriptNormP8_3Interval.1 manuscriptNormP8_3Interval.2 := by
  simpa only [manuscriptNormP8_3SubstituteRat, manuscriptNormP8_3Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num))

private theorem manuscriptNormP8_3SubstituteRat_upper :
    manuscriptNormP8_3SubstituteRat ≤ (1664463244265932879979458429 / 125000000000000000000000000000) :=
  manuscriptNormP8_3SubstituteRat_interval.2.trans manuscriptNormP8_3_rounded_endpoints.2

def manuscriptNormP8_4SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP8_4SubstituteRat_interval :
    manuscriptNormP8_4SubstituteRat ∈ Set.Icc manuscriptNormP8_4Interval.1 manuscriptNormP8_4Interval.2 := by
  simpa only [manuscriptNormP8_4SubstituteRat, manuscriptNormP8_4Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))

private theorem manuscriptNormP8_4SubstituteRat_upper :
    manuscriptNormP8_4SubstituteRat ≤ (-412726265283760513035682481 / 500000000000000000000000000000) :=
  manuscriptNormP8_4SubstituteRat_interval.2.trans manuscriptNormP8_4_rounded_endpoints.2

def manuscriptNormP8_5SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP8_5SubstituteRat_interval :
    manuscriptNormP8_5SubstituteRat ∈ Set.Icc manuscriptNormP8_5Interval.1 manuscriptNormP8_5Interval.2 := by
  simpa only [manuscriptNormP8_5SubstituteRat, manuscriptNormP8_5Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))

private theorem manuscriptNormP8_5SubstituteRat_upper :
    manuscriptNormP8_5SubstituteRat ≤ (-1695532107765573584766603021 / 1000000000000000000000000000000) :=
  manuscriptNormP8_5SubstituteRat_interval.2.trans manuscriptNormP8_5_rounded_endpoints.2

def manuscriptNormP8_6SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP8_6SubstituteRat_interval :
    manuscriptNormP8_6SubstituteRat ∈ Set.Icc manuscriptNormP8_6Interval.1 manuscriptNormP8_6Interval.2 := by
  simpa only [manuscriptNormP8_6SubstituteRat, manuscriptNormP8_6Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num))

private theorem manuscriptNormP8_6SubstituteRat_upper :
    manuscriptNormP8_6SubstituteRat ≤ (-271717843418425718753445767 / 200000000000000000000000000000) :=
  manuscriptNormP8_6SubstituteRat_interval.2.trans manuscriptNormP8_6_rounded_endpoints.2

def manuscriptNormP8_7SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709)

private theorem manuscriptNormP8_7SubstituteRat_interval :
    manuscriptNormP8_7SubstituteRat ∈ Set.Icc manuscriptNormP8_7Interval.1 manuscriptNormP8_7Interval.2 := by
  simpa only [manuscriptNormP8_7SubstituteRat, manuscriptNormP8_7Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709) (by norm_num))

private theorem manuscriptNormP8_7SubstituteRat_upper :
    manuscriptNormP8_7SubstituteRat ≤ (-345347922628817831427739889 / 200000000000000000000000000000) :=
  manuscriptNormP8_7SubstituteRat_interval.2.trans manuscriptNormP8_7_rounded_endpoints.2

def manuscriptNormP8_8SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871)

private theorem manuscriptNormP8_8SubstituteRat_interval :
    manuscriptNormP8_8SubstituteRat ∈ Set.Icc manuscriptNormP8_8Interval.1 manuscriptNormP8_8Interval.2 := by
  simpa only [manuscriptNormP8_8SubstituteRat, manuscriptNormP8_8Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871) (by norm_num))

private theorem manuscriptNormP8_8SubstituteRat_upper :
    manuscriptNormP8_8SubstituteRat ≤ (1110529536251391181828299469 / 1000000000000000000000000000000) :=
  manuscriptNormP8_8SubstituteRat_interval.2.trans manuscriptNormP8_8_rounded_endpoints.2

def manuscriptNormP8_9SubstituteRat : ℚ :=
  barrierWeightedComplexLogRat (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP8_9SubstituteRat_interval :
    manuscriptNormP8_9SubstituteRat ∈ Set.Icc manuscriptNormP8_9Interval.1 manuscriptNormP8_9Interval.2 := by
  simpa only [manuscriptNormP8_9SubstituteRat, manuscriptNormP8_9Interval, zero_div, div_one] using
    (manuscript_weightedComplexLogRat_interval (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num))

private theorem manuscriptNormP8_9SubstituteRat_upper :
    manuscriptNormP8_9SubstituteRat ≤ (4202023667396159430228982209 / 1000000000000000000000000000000) :=
  manuscriptNormP8_9SubstituteRat_interval.2.trans manuscriptNormP8_9_rounded_endpoints.2

def manuscriptNormPSubstituteRow8 : ℚ :=
  manuscriptNormP8_0SubstituteRat +
    manuscriptNormP8_1SubstituteRat +
    manuscriptNormP8_2SubstituteRat +
    manuscriptNormP8_3SubstituteRat +
    manuscriptNormP8_4SubstituteRat +
    manuscriptNormP8_5SubstituteRat +
    manuscriptNormP8_6SubstituteRat +
    manuscriptNormP8_7SubstituteRat +
    manuscriptNormP8_8SubstituteRat +
    manuscriptNormP8_9SubstituteRat

theorem manuscriptNormPSubstituteRow8_upper : manuscriptNormPSubstituteRow8 ≤ (17202400880231979705837607873 / 1000000000000000000000000000000) := by
  unfold manuscriptNormPSubstituteRow8
  linarith only [manuscriptNormP8_0SubstituteRat_upper,
    manuscriptNormP8_1SubstituteRat_upper,
    manuscriptNormP8_2SubstituteRat_upper,
    manuscriptNormP8_3SubstituteRat_upper,
    manuscriptNormP8_4SubstituteRat_upper,
    manuscriptNormP8_5SubstituteRat_upper,
    manuscriptNormP8_6SubstituteRat_upper,
    manuscriptNormP8_7SubstituteRat_upper,
    manuscriptNormP8_8SubstituteRat_upper,
    manuscriptNormP8_9SubstituteRat_upper]

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

private theorem manuscriptNormP8_0SubstituteRat_composition_error :
    |manuscriptNormP8_0Term - (manuscriptNormP8_0SubstituteRat : ℝ)| ≤ (((153887961761 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_0SubstituteRat ∈ Set.Icc manuscriptNormP8_0Interval.1 manuscriptNormP8_0Interval.2 := by
    simpa only [manuscriptNormP8_0SubstituteRat, manuscriptNormP8_0Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_0Interval.1 manuscriptNormP8_0Interval.2 manuscriptNormP8_0SubstituteRat
    (1190936412496125239808027647 / 500000000000000000000000000000) (476374564998450126700803411 / 200000000000000000000000000000) manuscriptNormP8_0Term
    manuscriptNormP8_0_exact_interval hq manuscriptNormP8_0_rounded_endpoints.1 manuscriptNormP8_0_rounded_endpoints.2
  have hw : ((476374564998450126700803411 / 200000000000000000000000000000) - (1190936412496125239808027647 / 500000000000000000000000000000) : ℚ) = (153887961761 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_1SubstituteRat_composition_error :
    |manuscriptNormP8_1Term - (manuscriptNormP8_1SubstituteRat : ℝ)| ≤ (((35292165581 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_1SubstituteRat ∈ Set.Icc manuscriptNormP8_1Interval.1 manuscriptNormP8_1Interval.2 := by
    simpa only [manuscriptNormP8_1SubstituteRat, manuscriptNormP8_1Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_1Interval.1 manuscriptNormP8_1Interval.2 manuscriptNormP8_1SubstituteRat
    (29020409128306298718006873 / 50000000000000000000000000000) (580408182566126009652303041 / 1000000000000000000000000000000) manuscriptNormP8_1Term
    manuscriptNormP8_1_exact_interval hq manuscriptNormP8_1_rounded_endpoints.1 manuscriptNormP8_1_rounded_endpoints.2
  have hw : ((580408182566126009652303041 / 1000000000000000000000000000000) - (29020409128306298718006873 / 50000000000000000000000000000) : ℚ) = (35292165581 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_2SubstituteRat_composition_error :
    |manuscriptNormP8_2Term - (manuscriptNormP8_2SubstituteRat : ℝ)| ≤ (((254113863 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_2SubstituteRat ∈ Set.Icc manuscriptNormP8_2Interval.1 manuscriptNormP8_2Interval.2 := by
    simpa only [manuscriptNormP8_2SubstituteRat, manuscriptNormP8_2Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_2Interval.1 manuscriptNormP8_2Interval.2 manuscriptNormP8_2SubstituteRat
    (1218174183467901772278121067 / 1000000000000000000000000000000) (121817418346790177253223493 / 100000000000000000000000000000) manuscriptNormP8_2Term
    manuscriptNormP8_2_exact_interval hq manuscriptNormP8_2_rounded_endpoints.1 manuscriptNormP8_2_rounded_endpoints.2
  have hw : ((121817418346790177253223493 / 100000000000000000000000000000) - (1218174183467901772278121067 / 1000000000000000000000000000000) : ℚ) = (254113863 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_3SubstituteRat_composition_error :
    |manuscriptNormP8_3Term - (manuscriptNormP8_3SubstituteRat : ℝ)| ≤ (((543953379 / 250000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_3SubstituteRat ∈ Set.Icc manuscriptNormP8_3Interval.1 manuscriptNormP8_3Interval.2 := by
    simpa only [manuscriptNormP8_3SubstituteRat, manuscriptNormP8_3Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_3Interval.1 manuscriptNormP8_3Interval.2 manuscriptNormP8_3SubstituteRat
    (3328926488531865759414963479 / 250000000000000000000000000000) (1664463244265932879979458429 / 125000000000000000000000000000) manuscriptNormP8_3Term
    manuscriptNormP8_3_exact_interval hq manuscriptNormP8_3_rounded_endpoints.1 manuscriptNormP8_3_rounded_endpoints.2
  have hw : ((1664463244265932879979458429 / 125000000000000000000000000000) - (3328926488531865759414963479 / 250000000000000000000000000000) : ℚ) = (543953379 / 250000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_4SubstituteRat_composition_error :
    |manuscriptNormP8_4Term - (manuscriptNormP8_4SubstituteRat : ℝ)| ≤ (((96501781 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_4SubstituteRat ∈ Set.Icc manuscriptNormP8_4Interval.1 manuscriptNormP8_4Interval.2 := by
    simpa only [manuscriptNormP8_4SubstituteRat, manuscriptNormP8_4Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_4Interval.1 manuscriptNormP8_4Interval.2 manuscriptNormP8_4SubstituteRat
    (-825452530567521026167866743 / 1000000000000000000000000000000) (-412726265283760513035682481 / 500000000000000000000000000000) manuscriptNormP8_4Term
    manuscriptNormP8_4_exact_interval hq manuscriptNormP8_4_rounded_endpoints.1 manuscriptNormP8_4_rounded_endpoints.2
  have hw : ((-412726265283760513035682481 / 500000000000000000000000000000) - (-825452530567521026167866743 / 1000000000000000000000000000000) : ℚ) = (96501781 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_5SubstituteRat_composition_error :
    |manuscriptNormP8_5Term - (manuscriptNormP8_5SubstituteRat : ℝ)| ≤ (((2332135007 / 100000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_5SubstituteRat ∈ Set.Icc manuscriptNormP8_5Interval.1 manuscriptNormP8_5Interval.2 := by
    simpa only [manuscriptNormP8_5SubstituteRat, manuscriptNormP8_5Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_5Interval.1 manuscriptNormP8_5Interval.2 manuscriptNormP8_5SubstituteRat
    (-1695532107765573608087953091 / 1000000000000000000000000000000) (-1695532107765573584766603021 / 1000000000000000000000000000000) manuscriptNormP8_5Term
    manuscriptNormP8_5_exact_interval hq manuscriptNormP8_5_rounded_endpoints.1 manuscriptNormP8_5_rounded_endpoints.2
  have hw : ((-1695532107765573584766603021 / 1000000000000000000000000000000) - (-1695532107765573608087953091 / 1000000000000000000000000000000) : ℚ) = (2332135007 / 100000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_6SubstituteRat_composition_error :
    |manuscriptNormP8_6Term - (manuscriptNormP8_6SubstituteRat : ℝ)| ≤ (((148518127 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_6SubstituteRat ∈ Set.Icc manuscriptNormP8_6Interval.1 manuscriptNormP8_6Interval.2 := by
    simpa only [manuscriptNormP8_6SubstituteRat, manuscriptNormP8_6Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_6Interval.1 manuscriptNormP8_6Interval.2 manuscriptNormP8_6SubstituteRat
    (-679294608546064296957873481 / 500000000000000000000000000000) (-271717843418425718753445767 / 200000000000000000000000000000) manuscriptNormP8_6Term
    manuscriptNormP8_6_exact_interval hq manuscriptNormP8_6_rounded_endpoints.1 manuscriptNormP8_6_rounded_endpoints.2
  have hw : ((-271717843418425718753445767 / 200000000000000000000000000000) - (-679294608546064296957873481 / 500000000000000000000000000000) : ℚ) = (148518127 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_7SubstituteRat_composition_error :
    |manuscriptNormP8_7Term - (manuscriptNormP8_7SubstituteRat : ℝ)| ≤ (((22122556297 / 500000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_7SubstituteRat ∈ Set.Icc manuscriptNormP8_7Interval.1 manuscriptNormP8_7Interval.2 := by
    simpa only [manuscriptNormP8_7SubstituteRat, manuscriptNormP8_7Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_7Interval.1 manuscriptNormP8_7Interval.2 manuscriptNormP8_7SubstituteRat
    (-1726739613144089201383812039 / 1000000000000000000000000000000) (-345347922628817831427739889 / 200000000000000000000000000000) manuscriptNormP8_7Term
    manuscriptNormP8_7_exact_interval hq manuscriptNormP8_7_rounded_endpoints.1 manuscriptNormP8_7_rounded_endpoints.2
  have hw : ((-345347922628817831427739889 / 200000000000000000000000000000) - (-1726739613144089201383812039 / 1000000000000000000000000000000) : ℚ) = (22122556297 / 500000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_8SubstituteRat_composition_error :
    |manuscriptNormP8_8Term - (manuscriptNormP8_8SubstituteRat : ℝ)| ≤ (((132055189 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_8SubstituteRat ∈ Set.Icc manuscriptNormP8_8Interval.1 manuscriptNormP8_8Interval.2 := by
    simpa only [manuscriptNormP8_8SubstituteRat, manuscriptNormP8_8Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_8Interval.1 manuscriptNormP8_8Interval.2 manuscriptNormP8_8SubstituteRat
    (27763238406284779542406107 / 25000000000000000000000000000) (1110529536251391181828299469 / 1000000000000000000000000000000) manuscriptNormP8_8Term
    manuscriptNormP8_8_exact_interval hq manuscriptNormP8_8_rounded_endpoints.1 manuscriptNormP8_8_rounded_endpoints.2
  have hw : ((1110529536251391181828299469 / 1000000000000000000000000000000) - (27763238406284779542406107 / 25000000000000000000000000000) : ℚ) = (132055189 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

private theorem manuscriptNormP8_9SubstituteRat_composition_error :
    |manuscriptNormP8_9Term - (manuscriptNormP8_9SubstituteRat : ℝ)| ≤ (((882059533 / 1000000000000000000000000000000) : ℚ) : ℝ) := by
  have hq : manuscriptNormP8_9SubstituteRat ∈ Set.Icc manuscriptNormP8_9Interval.1 manuscriptNormP8_9Interval.2 := by
    simpa only [manuscriptNormP8_9SubstituteRat, manuscriptNormP8_9Interval, zero_div, div_one] using
      (manuscript_weightedComplexLogRat_interval (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num))
  have h := manuscript_interval_abs_sub_le_rounded_width
    manuscriptNormP8_9Interval.1 manuscriptNormP8_9Interval.2 manuscriptNormP8_9SubstituteRat
    (1050505916849039857336730669 / 250000000000000000000000000000) (4202023667396159430228982209 / 1000000000000000000000000000000) manuscriptNormP8_9Term
    manuscriptNormP8_9_exact_interval hq manuscriptNormP8_9_rounded_endpoints.1 manuscriptNormP8_9_rounded_endpoints.2
  have hw : ((4202023667396159430228982209 / 1000000000000000000000000000000) - (1050505916849039857336730669 / 250000000000000000000000000000) : ℚ) = (882059533 / 1000000000000000000000000000000) := by norm_num
  simpa only [hw] using h

theorem manuscriptNormPCompositionRow8_error :
    |manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 8 (0, 0)) - (manuscriptNormPSubstituteRow8 : ℝ)| ≤ (((52087130403 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormP8_0SubstituteRat_composition_error
  have h1 := manuscriptNormP8_1SubstituteRat_composition_error
  have h2 := manuscriptNormP8_2SubstituteRat_composition_error
  have h3 := manuscriptNormP8_3SubstituteRat_composition_error
  have h4 := manuscriptNormP8_4SubstituteRat_composition_error
  have h5 := manuscriptNormP8_5SubstituteRat_composition_error
  have h6 := manuscriptNormP8_6SubstituteRat_composition_error
  have h7 := manuscriptNormP8_7SubstituteRat_composition_error
  have h8 := manuscriptNormP8_8SubstituteRat_composition_error
  have h9 := manuscriptNormP8_9SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  change |(manuscriptNormP8_0Term + (manuscriptNormP8_1Term + (manuscriptNormP8_2Term + (manuscriptNormP8_3Term + (manuscriptNormP8_4Term + (manuscriptNormP8_5Term + (manuscriptNormP8_6Term + (manuscriptNormP8_7Term + (manuscriptNormP8_8Term + (manuscriptNormP8_9Term + (0 : ℝ))))))))))) - (manuscriptNormPSubstituteRow8 : ℝ)| ≤ _
  unfold manuscriptNormPSubstituteRow8
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

def manuscriptNormP8_0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP8_0RoundedSubstituteRat_error :
    |(manuscriptNormP8_0SubstituteRat : ℝ) - (manuscriptNormP8_0RoundedSubstituteRat : ℝ)| ≤
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301) (by norm_num) (by norm_num)
  have hw : |(((-76806433087 / 78125000000000) : ℚ) : ℝ)| + |(((21224636816931 / 5000000000000000) : ℚ) : ℝ)| =
      (((26140248534499 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP8_1RoundedSubstituteRat_error :
    |(manuscriptNormP8_1SubstituteRat : ℝ) - (manuscriptNormP8_1RoundedSubstituteRat : ℝ)| ≤
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391) (by norm_num) (by norm_num)
  have hw : |(((-70453504591 / 312500000000000) : ℚ) : ℝ)| + |(((19469072932083 / 20000000000000000) : ℚ) : ℝ)| =
      (((23978097225907 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP8_2RoundedSubstituteRat_error :
    |(manuscriptNormP8_2SubstituteRat : ℝ) - (manuscriptNormP8_2RoundedSubstituteRat : ℝ)| ≤
      (((820264462342709 / 40000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110) (by norm_num) (by norm_num)
  have hw : |(((150530316475111 / 40000000000000000) : ℚ) : ℝ)| + |(((334867072933799 / 20000000000000000) : ℚ) : ℝ)| =
      (((820264462342709 / 40000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP8_3RoundedSubstituteRat_error :
    |(manuscriptNormP8_3SubstituteRat : ℝ) - (manuscriptNormP8_3RoundedSubstituteRat : ℝ)| ≤
      (((7720003947929 / 320000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890) (by norm_num) (by norm_num)
  have hw : |(((-85926283605499 / 8000000000000000) : ℚ) : ℝ)| + |(((53536907546363 / 4000000000000000) : ℚ) : ℝ)| =
      (((7720003947929 / 320000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP8_4RoundedSubstituteRat_error :
    |(manuscriptNormP8_4SubstituteRat : ℝ) - (manuscriptNormP8_4RoundedSubstituteRat : ℝ)| ≤
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910) (by norm_num) (by norm_num)
  have hw : |(((-57165053974051 / 40000000000000000) : ℚ) : ℝ)| + |(((-1441492417883 / 40000000000000000) : ℚ) : ℝ)| =
      (((29303273195967 / 20000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_5RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP8_5RoundedSubstituteRat_error :
    |(manuscriptNormP8_5SubstituteRat : ℝ) - (manuscriptNormP8_5RoundedSubstituteRat : ℝ)| ≤
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481) (by norm_num) (by norm_num)
  have hw : |(((51978482934179 / 40000000000000000) : ℚ) : ℝ)| + |(((23836077867557 / 40000000000000000) : ℚ) : ℝ)| =
      (((9476820100217 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_6RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP8_6RoundedSubstituteRat_error :
    |(manuscriptNormP8_6SubstituteRat : ℝ) - (manuscriptNormP8_6RoundedSubstituteRat : ℝ)| ≤
      (((12311306556531 / 5000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-43980712089603 / 20000000000000000) : ℚ) : ℝ)| + |(((5264514136521 / 20000000000000000) : ℚ) : ℝ)| =
      (((12311306556531 / 5000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_7RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709)

private theorem manuscriptNormP8_7RoundedSubstituteRat_error :
    |(manuscriptNormP8_7SubstituteRat : ℝ) - (manuscriptNormP8_7RoundedSubstituteRat : ℝ)| ≤
      (((24500663139 / 8000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709) (by norm_num) (by norm_num)
  have hw : |(((7437685121511 / 4000000000000000) : ℚ) : ℝ)| + |(((4812646447989 / 4000000000000000) : ℚ) : ℝ)| =
      (((24500663139 / 8000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871)

private theorem manuscriptNormP8_8RoundedSubstituteRat_error :
    |(manuscriptNormP8_8SubstituteRat : ℝ) - (manuscriptNormP8_8RoundedSubstituteRat : ℝ)| ≤
      (((116502281598737 / 40000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871) (by norm_num) (by norm_num)
  have hw : |(((78218217469073 / 40000000000000000) : ℚ) : ℝ)| + |(((299094251013 / 312500000000000) : ℚ) : ℝ)| =
      (((116502281598737 / 40000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormP8_9RoundedSubstituteRat : ℚ :=
  manuscriptRoundedWeightedComplexLogRat (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP8_9RoundedSubstituteRat_error :
    |(manuscriptNormP8_9SubstituteRat : ℝ) - (manuscriptNormP8_9RoundedSubstituteRat : ℝ)| ≤
      (((17416956232733 / 8000000000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h := manuscript_rounded_weighted_complex_log_error_le
    (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1) (by norm_num) (by norm_num)
  have hw : |(((-17416956232733 / 8000000000000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)| =
      (((17416956232733 / 8000000000000000) : ℚ) : ℝ) := by norm_num
  rw [hw] at h
  exact h

def manuscriptNormPRoundedSubstituteRow8 : ℚ :=
  manuscriptNormP8_0RoundedSubstituteRat +
    manuscriptNormP8_1RoundedSubstituteRat +
    manuscriptNormP8_2RoundedSubstituteRat +
    manuscriptNormP8_3RoundedSubstituteRat +
    manuscriptNormP8_4RoundedSubstituteRat +
    manuscriptNormP8_5RoundedSubstituteRat +
    manuscriptNormP8_6RoundedSubstituteRat +
    manuscriptNormP8_7RoundedSubstituteRat +
    manuscriptNormP8_8RoundedSubstituteRat +
    manuscriptNormP8_9RoundedSubstituteRat

theorem manuscriptNormPRoundedRow8_error :
    |(manuscriptNormPSubstituteRow8 : ℝ) - (manuscriptNormPRoundedSubstituteRow8 : ℝ)| ≤
      (((4064601682289 / 62500000000000) : ℚ) : ℝ) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscriptNormP8_0RoundedSubstituteRat_error
  have h1 := manuscriptNormP8_1RoundedSubstituteRat_error
  have h2 := manuscriptNormP8_2RoundedSubstituteRat_error
  have h3 := manuscriptNormP8_3RoundedSubstituteRat_error
  have h4 := manuscriptNormP8_4RoundedSubstituteRat_error
  have h5 := manuscriptNormP8_5RoundedSubstituteRat_error
  have h6 := manuscriptNormP8_6RoundedSubstituteRat_error
  have h7 := manuscriptNormP8_7RoundedSubstituteRat_error
  have h8 := manuscriptNormP8_8RoundedSubstituteRat_error
  have h9 := manuscriptNormP8_9RoundedSubstituteRat_error
  unfold manuscriptNormPSubstituteRow8 manuscriptNormPRoundedSubstituteRow8
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

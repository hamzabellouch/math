import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY0LogPrecisionGroup0
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY0LogPrecisionGroup1
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY0LogPrecisionGroup2
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case2PointData

def manuscriptCase2Y0FieldInterval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase2YRat Y0) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000)

theorem manuscriptCase2Y0_field_rounded :
    (-2177436308249863824458532082408183624303 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y0FieldInterval.1 ∧
      manuscriptCase2Y0FieldInterval.2 ≤ (-8709745232999455296494011876014342315463 / 10000000000000000000000000000000000000000) := by
  unfold manuscriptCase2Y0FieldInterval manuscriptYLogFieldInterval barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

private theorem manuscriptCase2Y0_YV_tail_eq :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y0 : ℝ))).sum =
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) +
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) +
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) +
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) +
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) := by
  apply barrierV2Tail_paired_sum
  intro i hi
  rw [barrierV2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV5_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV7_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV9_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV11_arg_regular

def manuscriptCase2Y0Interval : ℚ × ℚ :=
  (manuscriptCase2Y0FieldInterval.1 + 1 * manuscriptCase2Y0YV0Interval.1 + 1 * manuscriptCase2Y0YV1Interval.1 + 1 * manuscriptCase2Y0YV2Interval.1 + 1 * manuscriptCase2Y0YV3Interval.1 + 1 * manuscriptCase2Y0YV4Interval.1 + 2 * manuscriptCase2Y0YV5Interval.1 + 2 * manuscriptCase2Y0YV7Interval.1 + 2 * manuscriptCase2Y0YV9Interval.1 + 2 * manuscriptCase2Y0YV11Interval.1,
   manuscriptCase2Y0FieldInterval.2 + 1 * manuscriptCase2Y0YV0Interval.2 + 1 * manuscriptCase2Y0YV1Interval.2 + 1 * manuscriptCase2Y0YV2Interval.2 + 1 * manuscriptCase2Y0YV3Interval.2 + 1 * manuscriptCase2Y0YV4Interval.2 + 2 * manuscriptCase2Y0YV5Interval.2 + 2 * manuscriptCase2Y0YV7Interval.2 + 2 * manuscriptCase2Y0YV9Interval.2 + 2 * manuscriptCase2Y0YV11Interval.2)

theorem manuscript_case2Y0_interval :
    barrierCase2Y (Y0 : ℝ) ∈ Set.Icc (manuscriptCase2Y0Interval.1 : ℝ) (manuscriptCase2Y0Interval.2 : ℝ) := by
  have he := barrierCase2Y_eval_rat Y0 (by norm_num [Y0])
  rw [manuscriptCase2Y0_YV_tail_eq] at he
  have hf := manuscript_y_log_field_interval (barrierCase2YRat Y0)
    (Y0 : ℝ) (1 - (Y0 : ℝ)) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) Y0_normalizations.1 Y0_normalizations.2
  change _ ∈ Set.Icc (manuscriptCase2Y0FieldInterval.1 : ℝ) (manuscriptCase2Y0FieldInterval.2 : ℝ) at hf
  constructor
  · change (manuscriptCase2Y0Interval.1 : ℝ) ≤ _
    dsimp only [manuscriptCase2Y0Interval]
    push_cast
    linarith only [he, hf.1,
      manuscriptCase2Y0YV0_exact_interval.1,
      manuscriptCase2Y0YV1_exact_interval.1,
      manuscriptCase2Y0YV2_exact_interval.1,
      manuscriptCase2Y0YV3_exact_interval.1,
      manuscriptCase2Y0YV4_exact_interval.1,
      manuscriptCase2Y0YV5_exact_interval.1,
      manuscriptCase2Y0YV7_exact_interval.1,
      manuscriptCase2Y0YV9_exact_interval.1,
      manuscriptCase2Y0YV11_exact_interval.1]
  · change _ ≤ (manuscriptCase2Y0Interval.2 : ℝ)
    dsimp only [manuscriptCase2Y0Interval]
    push_cast
    linarith only [he, hf.2,
      manuscriptCase2Y0YV0_exact_interval.2,
      manuscriptCase2Y0YV1_exact_interval.2,
      manuscriptCase2Y0YV2_exact_interval.2,
      manuscriptCase2Y0YV3_exact_interval.2,
      manuscriptCase2Y0YV4_exact_interval.2,
      manuscriptCase2Y0YV5_exact_interval.2,
      manuscriptCase2Y0YV7_exact_interval.2,
      manuscriptCase2Y0YV9_exact_interval.2,
      manuscriptCase2Y0YV11_exact_interval.2]

theorem manuscript_case2Y0_rounded_endpoints :
    (-2011183014558492341931751682382756603193 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y0Interval.1 ∧ manuscriptCase2Y0Interval.2 ≤ (-1005591507279246163107769926321460641769 / 625000000000000000000000000000000000000) := by
  constructor
  · dsimp only [manuscriptCase2Y0Interval]
    linarith only [manuscriptCase2Y0_field_rounded.1,
      manuscriptCase2Y0YV0_rounded_endpoints.1,
      manuscriptCase2Y0YV1_rounded_endpoints.1,
      manuscriptCase2Y0YV2_rounded_endpoints.1,
      manuscriptCase2Y0YV3_rounded_endpoints.1,
      manuscriptCase2Y0YV4_rounded_endpoints.1,
      manuscriptCase2Y0YV5_rounded_endpoints.1,
      manuscriptCase2Y0YV7_rounded_endpoints.1,
      manuscriptCase2Y0YV9_rounded_endpoints.1,
      manuscriptCase2Y0YV11_rounded_endpoints.1]
  · dsimp only [manuscriptCase2Y0Interval]
    linarith only [manuscriptCase2Y0_field_rounded.2,
      manuscriptCase2Y0YV0_rounded_endpoints.2,
      manuscriptCase2Y0YV1_rounded_endpoints.2,
      manuscriptCase2Y0YV2_rounded_endpoints.2,
      manuscriptCase2Y0YV3_rounded_endpoints.2,
      manuscriptCase2Y0YV4_rounded_endpoints.2,
      manuscriptCase2Y0YV5_rounded_endpoints.2,
      manuscriptCase2Y0YV7_rounded_endpoints.2,
      manuscriptCase2Y0YV9_rounded_endpoints.2,
      manuscriptCase2Y0YV11_rounded_endpoints.2]

def manuscriptCase2Y0PrintedUpper : ℚ := (-804473205823 / 500000000000)

theorem manuscript_case2Y0_endpoint_lt_printed :
    manuscriptCase2Y0Interval.2 < manuscriptCase2Y0PrintedUpper :=
  manuscript_case2Y0_rounded_endpoints.2.trans_lt (by decide +kernel)

theorem manuscript_case2Y0_interval_width :
    manuscriptCase2Y0Interval.2 - manuscriptCase2Y0Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  have hw : (-1005591507279246163107769926321460641769 / 625000000000000000000000000000000000000) - (-2011183014558492341931751682382756603193 / 1250000000000000000000000000000000000000) < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by decide +kernel
  linarith only [hw, manuscript_case2Y0_rounded_endpoints.1, manuscript_case2Y0_rounded_endpoints.2]

theorem manuscript_case2Y0_printed_upper :
    barrierCase2Y (Y0 : ℝ) < (manuscriptCase2Y0PrintedUpper : ℝ) :=
  manuscript_case2Y0_interval.2.trans_lt ((Rat.cast_lt (K := ℝ)).2 manuscript_case2Y0_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y0SubstituteRat : ℚ :=
  barrierCase2YApproxRat Case2PointData.Y0 (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) +
    (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-3) (-(0)) (2407935099937449820321 / 1953125000000000000000) (-(-3439854639 / 48950000000))) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000)) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-5) (-(0)) (23192638458207386881 / 19531250000000000000) (-(-41779611 / 250000000))) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197)) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-7) (-(-1)) (2218703626544613343281 / 1953125000000000000000) (-(9047010803 / 20277989197))) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323)) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-9) (-(-1)) (216102260916290816329 / 190734863281250000000) (-(-928772323 / 20768772323)))

theorem manuscript_case2Y0_substitute_interval :
    manuscriptCase2Y0SubstituteRat ∈ Set.Icc manuscriptCase2Y0Interval.1 manuscriptCase2Y0Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase2YRat Case2PointData.Y0) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) (by norm_num) (by norm_num)
  change (barrierCase2YApproxRat Case2PointData.Y0 (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000)) ∈ Set.Icc manuscriptCase2Y0FieldInterval.1 manuscriptCase2Y0FieldInterval.2 at hf
  have ht0 := manuscript_weightedComplexLogRat_interval (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y0YV0Interval.1 manuscriptCase2Y0YV0Interval.2 at ht0
  have ht1 := manuscript_weightedComplexLogRat_interval (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y0YV1Interval.1 manuscriptCase2Y0YV1Interval.2 at ht1
  have ht2 := manuscript_weightedComplexLogRat_interval (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y0YV2Interval.1 manuscriptCase2Y0YV2Interval.2 at ht2
  have ht3 := manuscript_weightedComplexLogRat_interval (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y0YV3Interval.1 manuscriptCase2Y0YV3Interval.2 at ht3
  have ht4 := manuscript_weightedComplexLogRat_interval (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y0YV4Interval.1 manuscriptCase2Y0YV4Interval.2 at ht4
  have ht5 := manuscript_weightedComplexLogRat_interval (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000) (by norm_num)
  change (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000)) ∈ Set.Icc manuscriptCase2Y0YV5Interval.1 manuscriptCase2Y0YV5Interval.2 at ht5
  have hc5 := manuscript_weightedComplexLogRat_conj (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000)
  have ht6 := manuscript_weightedComplexLogRat_interval (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000) (by norm_num)
  change (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000)) ∈ Set.Icc manuscriptCase2Y0YV7Interval.1 manuscriptCase2Y0YV7Interval.2 at ht6
  have hc6 := manuscript_weightedComplexLogRat_conj (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000)
  have ht7 := manuscript_weightedComplexLogRat_interval (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197) (by norm_num)
  change (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197)) ∈ Set.Icc manuscriptCase2Y0YV9Interval.1 manuscriptCase2Y0YV9Interval.2 at ht7
  have hc7 := manuscript_weightedComplexLogRat_conj (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197)
  have ht8 := manuscript_weightedComplexLogRat_interval (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323) (by norm_num)
  change (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323)) ∈ Set.Icc manuscriptCase2Y0YV11Interval.1 manuscriptCase2Y0YV11Interval.2 at ht8
  have hc8 := manuscript_weightedComplexLogRat_conj (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323)
  constructor
  · change manuscriptCase2Y0Interval.1 ≤ manuscriptCase2Y0SubstituteRat
    dsimp only [manuscriptCase2Y0Interval, manuscriptCase2Y0SubstituteRat]
    linarith only [hf.1, ht0.1, ht1.1, ht2.1, ht3.1, ht4.1, ht5.1, ht6.1, ht7.1, ht8.1, hc5, hc6, hc7, hc8]
  · change manuscriptCase2Y0SubstituteRat ≤ manuscriptCase2Y0Interval.2
    dsimp only [manuscriptCase2Y0Interval, manuscriptCase2Y0SubstituteRat]
    linarith only [hf.2, ht0.2, ht1.2, ht2.2, ht3.2, ht4.2, ht5.2, ht6.2, ht7.2, ht8.2, hc5, hc6, hc7, hc8]

theorem manuscript_case2Y0_substitute_cutoff :
    manuscriptCase2Y0SubstituteRat < ((-160891 / 100000) : ℚ) := by
  have hp : manuscriptCase2Y0PrintedUpper < ((-160891 / 100000) : ℚ) := by norm_num [manuscriptCase2Y0PrintedUpper]
  exact manuscript_case2Y0_substitute_interval.2.trans_lt (manuscript_case2Y0_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y0) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) +
    (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-3) (-(0)) (2407935099937449820321 / 1953125000000000000000) (-(-3439854639 / 48950000000))) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000)) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-5) (-(0)) (23192638458207386881 / 19531250000000000000) (-(-41779611 / 250000000))) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197)) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-7) (-(-1)) (2218703626544613343281 / 1953125000000000000000) (-(9047010803 / 20277989197))) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323)) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-9) (-(-1)) (216102260916290816329 / 190734863281250000000) (-(-928772323 / 20768772323)))

theorem manuscript_case2Y0_additional_rounding_error :
    |(manuscriptCase2Y0SubstituteRat : ℝ) - (manuscriptCase2Y0RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase2YApproxRat Case2PointData.Y0 (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000)
  let r0 : ℚ := manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y0) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000)
  let e0 : ℝ := ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep)
  let a1 : ℚ := (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1))
  let r1 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1))
  let e1 : ℝ := (|(((-15199211 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a2 : ℚ := (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1))
  let r2 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1))
  let e2 : ℝ := (|(((-2225831 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a3 : ℚ := (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1))
  let r3 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1))
  let e3 : ℝ := (|(((-1272699 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a4 : ℚ := (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1))
  let r4 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1))
  let e4 : ℝ := (|(((2466317 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a5 : ℚ := (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1))
  let r5 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1))
  let e5 : ℝ := (|(((-11618157 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a6 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000))
  let r6 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000))
  let e6 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-600749 / 3125000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a7 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-3) (-(0)) (2407935099937449820321 / 1953125000000000000000) (-(-3439854639 / 48950000000)))
  let r7 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-3) (-(0)) (2407935099937449820321 / 1953125000000000000000) (-(-3439854639 / 48950000000)))
  let e7 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-(-600749 / 3125000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a8 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000))
  let r8 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000))
  let e8 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-15094393 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a9 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-5) (-(0)) (23192638458207386881 / 19531250000000000000) (-(-41779611 / 250000000)))
  let r9 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-5) (-(0)) (23192638458207386881 / 19531250000000000000) (-(-41779611 / 250000000)))
  let e9 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-(-15094393 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a10 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197))
  let r10 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197))
  let e10 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((5956127 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a11 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-7) (-(-1)) (2218703626544613343281 / 1953125000000000000000) (-(9047010803 / 20277989197)))
  let r11 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-7) (-(-1)) (2218703626544613343281 / 1953125000000000000000) (-(9047010803 / 20277989197)))
  let e11 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((-(5956127 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a12 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323))
  let r12 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323))
  let e12 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-21715849 / 200000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a13 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-9) (-(-1)) (216102260916290816329 / 190734863281250000000) (-(-928772323 / 20768772323)))
  let r13 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-9) (-(-1)) (216102260916290816329 / 190734863281250000000) (-(-928772323 / 20768772323)))
  let e13 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-(-21715849 / 200000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_y_field_error_le (barrierCase2YRat Case2PointData.Y0) (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) (by norm_num) (by norm_num)
  have h1 : |(a1 : ℝ) - (r1 : ℝ)| ≤ e1 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h2 : |(a2 : ℝ) - (r2 : ℝ)| ≤ e2 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1) (by norm_num) (by norm_num)
  have h3 : |(a3 : ℝ) - (r3 : ℝ)| ≤ e3 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h4 : |(a4 : ℝ) - (r4 : ℝ)| ≤ e4 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h5 : |(a5 : ℝ) - (r5 : ℝ)| ≤ e5 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h6 : |(a6 : ℝ) - (r6 : ℝ)| ≤ e6 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000) (by norm_num) (by norm_num)
  have h7 : |(a7 : ℝ) - (r7 : ℝ)| ≤ e7 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-(-600749 / 3125000)) (-3) (-(0)) (2407935099937449820321 / 1953125000000000000000) (-(-3439854639 / 48950000000)) (by norm_num) (by norm_num)
  have h8 : |(a8 : ℝ) - (r8 : ℝ)| ≤ e8 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000) (by norm_num) (by norm_num)
  have h9 : |(a9 : ℝ) - (r9 : ℝ)| ≤ e9 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-(-15094393 / 100000000)) (-5) (-(0)) (23192638458207386881 / 19531250000000000000) (-(-41779611 / 250000000)) (by norm_num) (by norm_num)
  have h10 : |(a10 : ℝ) - (r10 : ℝ)| ≤ e10 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197) (by norm_num) (by norm_num)
  have h11 : |(a11 : ℝ) - (r11 : ℝ)| ≤ e11 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (-(5956127 / 100000000)) (-7) (-(-1)) (2218703626544613343281 / 1953125000000000000000) (-(9047010803 / 20277989197)) (by norm_num) (by norm_num)
  have h12 : |(a12 : ℝ) - (r12 : ℝ)| ≤ e12 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323) (by norm_num) (by norm_num)
  have h13 : |(a13 : ℝ) - (r13 : ℝ)| ≤ e13 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-(-21715849 / 200000000)) (-9) (-(-1)) (216102260916290816329 / 190734863281250000000) (-(-928772323 / 20768772323)) (by norm_num) (by norm_num)
  have hs1 := manuscript_rat_add_rounding_error (a0) (r0) a1 r1 h0 h1
  have hs2 := manuscript_rat_add_rounding_error (a0 + a1) (r0 + r1) a2 r2 hs1 h2
  have hs3 := manuscript_rat_add_rounding_error (a0 + a1 + a2) (r0 + r1 + r2) a3 r3 hs2 h3
  have hs4 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3) (r0 + r1 + r2 + r3) a4 r4 hs3 h4
  have hs5 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4) (r0 + r1 + r2 + r3 + r4) a5 r5 hs4 h5
  have hs6 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5) (r0 + r1 + r2 + r3 + r4 + r5) a6 r6 hs5 h6
  have hs7 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6) (r0 + r1 + r2 + r3 + r4 + r5 + r6) a7 r7 hs6 h7
  have hs8 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7) a8 r8 hs7 h8
  have hs9 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8) a9 r9 hs8 h9
  have hs10 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9) a10 r10 hs9 h10
  have hs11 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10) a11 r11 hs10 h11
  have hs12 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11) a12 r12 hs11 h12
  have hs13 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12) a13 r13 hs12 h13
  have hbudget : e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, manuscriptTermRoundStep]
  change |(manuscriptCase2Y0SubstituteRat : ℝ) - (manuscriptCase2Y0RoundedSubstituteRat : ℝ)| ≤ e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 at hs13
  exact hs13.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case2Y0_actual_substitution_error :
    |barrierCase2Y (Case2PointData.Y0 : ℝ) - (manuscriptCase2Y0SubstituteRat : ℝ)| < ((14 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase2Y0Interval.2 - manuscriptCase2Y0Interval.1 < ((14 / 1000000000000000) : ℚ) :=
    manuscript_case2Y0_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase2Y0Interval.1 manuscriptCase2Y0Interval.2 manuscriptCase2Y0SubstituteRat
    (barrierCase2Y (Case2PointData.Y0 : ℝ)) (14 / 1000000000000000)
    manuscript_case2Y0_interval manuscript_case2Y0_substitute_interval hw

end InternalCatalan

end

end

end OAI

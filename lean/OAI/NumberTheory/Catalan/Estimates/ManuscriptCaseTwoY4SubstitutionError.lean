import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY4LogPrecisionGroup0
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY4LogPrecisionGroup1
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY4LogPrecisionGroup2
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case2PointData

def manuscriptCase2Y4FieldInterval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase2YRat Y4) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000)

theorem manuscriptCase2Y4_field_rounded :
    (-5325664566255366167074466715150351134909 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4FieldInterval.1 ∧
      manuscriptCase2Y4FieldInterval.2 ≤ (-2662832283127683083185522513143995509613 / 5000000000000000000000000000000000000000) := by
  unfold manuscriptCase2Y4FieldInterval manuscriptYLogFieldInterval barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

private theorem manuscriptCase2Y4_YV_tail_eq :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y4 : ℝ))).sum =
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) +
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) +
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) +
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) +
      barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) := by
  apply barrierV2Tail_paired_sum
  intro i hi
  rw [barrierV2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV5_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV7_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV9_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y4YV11_arg_regular

def manuscriptCase2Y4Interval : ℚ × ℚ :=
  (manuscriptCase2Y4FieldInterval.1 + 1 * manuscriptCase2Y4YV0Interval.1 + 1 * manuscriptCase2Y4YV1Interval.1 + 1 * manuscriptCase2Y4YV2Interval.1 + 1 * manuscriptCase2Y4YV3Interval.1 + 1 * manuscriptCase2Y4YV4Interval.1 + 2 * manuscriptCase2Y4YV5Interval.1 + 2 * manuscriptCase2Y4YV7Interval.1 + 2 * manuscriptCase2Y4YV9Interval.1 + 2 * manuscriptCase2Y4YV11Interval.1,
   manuscriptCase2Y4FieldInterval.2 + 1 * manuscriptCase2Y4YV0Interval.2 + 1 * manuscriptCase2Y4YV1Interval.2 + 1 * manuscriptCase2Y4YV2Interval.2 + 1 * manuscriptCase2Y4YV3Interval.2 + 1 * manuscriptCase2Y4YV4Interval.2 + 2 * manuscriptCase2Y4YV5Interval.2 + 2 * manuscriptCase2Y4YV7Interval.2 + 2 * manuscriptCase2Y4YV9Interval.2 + 2 * manuscriptCase2Y4YV11Interval.2)

theorem manuscript_case2Y4_interval :
    barrierCase2Y (Y4 : ℝ) ∈ Set.Icc (manuscriptCase2Y4Interval.1 : ℝ) (manuscriptCase2Y4Interval.2 : ℝ) := by
  have he := barrierCase2Y_eval_rat Y4 (by norm_num [Y4])
  rw [manuscriptCase2Y4_YV_tail_eq] at he
  have hf := manuscript_y_log_field_interval (barrierCase2YRat Y4)
    (Y4 : ℝ) (1 - (Y4 : ℝ)) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) Y4_normalizations.1 Y4_normalizations.2
  change _ ∈ Set.Icc (manuscriptCase2Y4FieldInterval.1 : ℝ) (manuscriptCase2Y4FieldInterval.2 : ℝ) at hf
  constructor
  · change (manuscriptCase2Y4Interval.1 : ℝ) ≤ _
    dsimp only [manuscriptCase2Y4Interval]
    push_cast
    linarith only [he, hf.1,
      manuscriptCase2Y4YV0_exact_interval.1,
      manuscriptCase2Y4YV1_exact_interval.1,
      manuscriptCase2Y4YV2_exact_interval.1,
      manuscriptCase2Y4YV3_exact_interval.1,
      manuscriptCase2Y4YV4_exact_interval.1,
      manuscriptCase2Y4YV5_exact_interval.1,
      manuscriptCase2Y4YV7_exact_interval.1,
      manuscriptCase2Y4YV9_exact_interval.1,
      manuscriptCase2Y4YV11_exact_interval.1]
  · change _ ≤ (manuscriptCase2Y4Interval.2 : ℝ)
    dsimp only [manuscriptCase2Y4Interval]
    push_cast
    linarith only [he, hf.2,
      manuscriptCase2Y4YV0_exact_interval.2,
      manuscriptCase2Y4YV1_exact_interval.2,
      manuscriptCase2Y4YV2_exact_interval.2,
      manuscriptCase2Y4YV3_exact_interval.2,
      manuscriptCase2Y4YV4_exact_interval.2,
      manuscriptCase2Y4YV5_exact_interval.2,
      manuscriptCase2Y4YV7_exact_interval.2,
      manuscriptCase2Y4YV9_exact_interval.2,
      manuscriptCase2Y4YV11_exact_interval.2]

theorem manuscript_case2Y4_rounded_endpoints :
    (-16089604265005731403455776759208483153437 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4Interval.1 ∧ manuscriptCase2Y4Interval.2 ≤ (-16089604265005730753872921783268226403599 / 10000000000000000000000000000000000000000) := by
  constructor
  · dsimp only [manuscriptCase2Y4Interval]
    linarith only [manuscriptCase2Y4_field_rounded.1,
      manuscriptCase2Y4YV0_rounded_endpoints.1,
      manuscriptCase2Y4YV1_rounded_endpoints.1,
      manuscriptCase2Y4YV2_rounded_endpoints.1,
      manuscriptCase2Y4YV3_rounded_endpoints.1,
      manuscriptCase2Y4YV4_rounded_endpoints.1,
      manuscriptCase2Y4YV5_rounded_endpoints.1,
      manuscriptCase2Y4YV7_rounded_endpoints.1,
      manuscriptCase2Y4YV9_rounded_endpoints.1,
      manuscriptCase2Y4YV11_rounded_endpoints.1]
  · dsimp only [manuscriptCase2Y4Interval]
    linarith only [manuscriptCase2Y4_field_rounded.2,
      manuscriptCase2Y4YV0_rounded_endpoints.2,
      manuscriptCase2Y4YV1_rounded_endpoints.2,
      manuscriptCase2Y4YV2_rounded_endpoints.2,
      manuscriptCase2Y4YV3_rounded_endpoints.2,
      manuscriptCase2Y4YV4_rounded_endpoints.2,
      manuscriptCase2Y4YV5_rounded_endpoints.2,
      manuscriptCase2Y4YV7_rounded_endpoints.2,
      manuscriptCase2Y4YV9_rounded_endpoints.2,
      manuscriptCase2Y4YV11_rounded_endpoints.2]

def manuscriptCase2Y4PrintedUpper : ℚ := (-3217920853 / 2000000000)

theorem manuscript_case2Y4_endpoint_lt_printed :
    manuscriptCase2Y4Interval.2 < manuscriptCase2Y4PrintedUpper :=
  manuscript_case2Y4_rounded_endpoints.2.trans_lt (by decide +kernel)

theorem manuscript_case2Y4_interval_width :
    manuscriptCase2Y4Interval.2 - manuscriptCase2Y4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  have hw : (-16089604265005730753872921783268226403599 / 10000000000000000000000000000000000000000) - (-16089604265005731403455776759208483153437 / 10000000000000000000000000000000000000000) < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by decide +kernel
  linarith only [hw, manuscript_case2Y4_rounded_endpoints.1, manuscript_case2Y4_rounded_endpoints.2]

theorem manuscript_case2Y4_printed_upper :
    barrierCase2Y (Y4 : ℝ) < (manuscriptCase2Y4PrintedUpper : ℝ) :=
  manuscript_case2Y4_interval.2.trans_lt ((Rat.cast_lt (K := ℝ)).2 manuscript_case2Y4_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y4SubstituteRat : ℚ :=
  barrierCase2YApproxRat Case2PointData.Y4 (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) +
    (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-2) (-(-1)) (4152935100111231215521 / 3906250000000000000000) (-(7035413039 / 90864586961))) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991)) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-3) (-(-2)) (116121632550302254081 / 78125000000000000000) (-(4750000000 / 9672596991))) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603)) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-3) (-(-2)) (44072316385479339890481 / 31250000000000000000000) (-(14662500000 / 68424667603))) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877)) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-3) (-(-2)) (17573173268562009901129 / 12207031250000000000000) (-(9920000000 / 132192158877)))

theorem manuscript_case2Y4_substitute_interval :
    manuscriptCase2Y4SubstituteRat ∈ Set.Icc manuscriptCase2Y4Interval.1 manuscriptCase2Y4Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase2YRat Case2PointData.Y4) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) (by norm_num) (by norm_num)
  change (barrierCase2YApproxRat Case2PointData.Y4 (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000)) ∈ Set.Icc manuscriptCase2Y4FieldInterval.1 manuscriptCase2Y4FieldInterval.2 at hf
  have ht0 := manuscript_weightedComplexLogRat_interval (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y4YV0Interval.1 manuscriptCase2Y4YV0Interval.2 at ht0
  have ht1 := manuscript_weightedComplexLogRat_interval (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y4YV1Interval.1 manuscriptCase2Y4YV1Interval.2 at ht1
  have ht2 := manuscript_weightedComplexLogRat_interval (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y4YV2Interval.1 manuscriptCase2Y4YV2Interval.2 at ht2
  have ht3 := manuscript_weightedComplexLogRat_interval (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y4YV3Interval.1 manuscriptCase2Y4YV3Interval.2 at ht3
  have ht4 := manuscript_weightedComplexLogRat_interval (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y4YV4Interval.1 manuscriptCase2Y4YV4Interval.2 at ht4
  have ht5 := manuscript_weightedComplexLogRat_interval (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961) (by norm_num)
  change (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961)) ∈ Set.Icc manuscriptCase2Y4YV5Interval.1 manuscriptCase2Y4YV5Interval.2 at ht5
  have hc5 := manuscript_weightedComplexLogRat_conj (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961)
  have ht6 := manuscript_weightedComplexLogRat_interval (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991) (by norm_num)
  change (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991)) ∈ Set.Icc manuscriptCase2Y4YV7Interval.1 manuscriptCase2Y4YV7Interval.2 at ht6
  have hc6 := manuscript_weightedComplexLogRat_conj (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991)
  have ht7 := manuscript_weightedComplexLogRat_interval (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603) (by norm_num)
  change (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603)) ∈ Set.Icc manuscriptCase2Y4YV9Interval.1 manuscriptCase2Y4YV9Interval.2 at ht7
  have hc7 := manuscript_weightedComplexLogRat_conj (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603)
  have ht8 := manuscript_weightedComplexLogRat_interval (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877) (by norm_num)
  change (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877)) ∈ Set.Icc manuscriptCase2Y4YV11Interval.1 manuscriptCase2Y4YV11Interval.2 at ht8
  have hc8 := manuscript_weightedComplexLogRat_conj (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877)
  constructor
  · change manuscriptCase2Y4Interval.1 ≤ manuscriptCase2Y4SubstituteRat
    dsimp only [manuscriptCase2Y4Interval, manuscriptCase2Y4SubstituteRat]
    linarith only [hf.1, ht0.1, ht1.1, ht2.1, ht3.1, ht4.1, ht5.1, ht6.1, ht7.1, ht8.1, hc5, hc6, hc7, hc8]
  · change manuscriptCase2Y4SubstituteRat ≤ manuscriptCase2Y4Interval.2
    dsimp only [manuscriptCase2Y4Interval, manuscriptCase2Y4SubstituteRat]
    linarith only [hf.2, ht0.2, ht1.2, ht2.2, ht3.2, ht4.2, ht5.2, ht6.2, ht7.2, ht8.2, hc5, hc6, hc7, hc8]

theorem manuscript_case2Y4_substitute_cutoff :
    manuscriptCase2Y4SubstituteRat < ((-160891 / 100000) : ℚ) := by
  have hp : manuscriptCase2Y4PrintedUpper < ((-160891 / 100000) : ℚ) := by norm_num [manuscriptCase2Y4PrintedUpper]
  exact manuscript_case2Y4_substitute_interval.2.trans_lt (manuscript_case2Y4_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y4) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) +
    (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-2) (-(-1)) (4152935100111231215521 / 3906250000000000000000) (-(7035413039 / 90864586961))) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991)) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-3) (-(-2)) (116121632550302254081 / 78125000000000000000) (-(4750000000 / 9672596991))) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603)) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-3) (-(-2)) (44072316385479339890481 / 31250000000000000000000) (-(14662500000 / 68424667603))) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877)) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-3) (-(-2)) (17573173268562009901129 / 12207031250000000000000) (-(9920000000 / 132192158877)))

theorem manuscript_case2Y4_additional_rounding_error :
    |(manuscriptCase2Y4SubstituteRat : ℝ) - (manuscriptCase2Y4RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase2YApproxRat Case2PointData.Y4 (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000)
  let r0 : ℚ := manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y4) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000)
  let e0 : ℝ := ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep)
  let a1 : ℚ := (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1))
  let r1 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1))
  let e1 : ℝ := (|(((-15199211 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a2 : ℚ := (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1))
  let r2 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1))
  let e2 : ℝ := (|(((-2225831 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a3 : ℚ := (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1))
  let r3 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1))
  let e3 : ℝ := (|(((-1272699 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a4 : ℚ := (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1))
  let r4 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1))
  let e4 : ℝ := (|(((2466317 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a5 : ℚ := (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1))
  let r5 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1))
  let e5 : ℝ := (|(((-11618157 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a6 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961))
  let r6 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961))
  let e6 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-600749 / 3125000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a7 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-2) (-(-1)) (4152935100111231215521 / 3906250000000000000000) (-(7035413039 / 90864586961)))
  let r7 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (-2) (-(-1)) (4152935100111231215521 / 3906250000000000000000) (-(7035413039 / 90864586961)))
  let e7 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-(-600749 / 3125000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a8 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991))
  let r8 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991))
  let e8 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-15094393 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a9 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-3) (-(-2)) (116121632550302254081 / 78125000000000000000) (-(4750000000 / 9672596991)))
  let r9 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (-3) (-(-2)) (116121632550302254081 / 78125000000000000000) (-(4750000000 / 9672596991)))
  let e9 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-(-15094393 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a10 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603))
  let r10 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603))
  let e10 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((5956127 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a11 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-3) (-(-2)) (44072316385479339890481 / 31250000000000000000000) (-(14662500000 / 68424667603)))
  let r11 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (-3) (-(-2)) (44072316385479339890481 / 31250000000000000000000) (-(14662500000 / 68424667603)))
  let e11 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((-(5956127 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a12 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877))
  let r12 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877))
  let e12 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-21715849 / 200000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a13 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-3) (-(-2)) (17573173268562009901129 / 12207031250000000000000) (-(9920000000 / 132192158877)))
  let r13 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (-3) (-(-2)) (17573173268562009901129 / 12207031250000000000000) (-(9920000000 / 132192158877)))
  let e13 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-(-21715849 / 200000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_y_field_error_le (barrierCase2YRat Case2PointData.Y4) (-3) (-1) (1074732999 / 625000000) (3925267001 / 2500000000) (by norm_num) (by norm_num)
  have h1 : |(a1 : ℝ) - (r1 : ℝ)| ≤ e1 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h2 : |(a2 : ℝ) - (r2 : ℝ)| ≤ e2 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h3 : |(a3 : ℝ) - (r3 : ℝ)| ≤ e3 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h4 : |(a4 : ℝ) - (r4 : ℝ)| ≤ e4 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2466317 / 50000000) (0 / 1) (1) (0) (5580847934774121774361 / 5000000000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h5 : |(a5 : ℝ) - (r5 : ℝ)| ≤ e5 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-11618157 / 100000000) (0 / 1) (1) (0) (233180667104431689901129 / 195312500000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h6 : |(a6 : ℝ) - (r6 : ℝ)| ≤ e6 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (4152935100111231215521 / 3906250000000000000000) (7035413039 / 90864586961) (by norm_num) (by norm_num)
  have h7 : |(a7 : ℝ) - (r7 : ℝ)| ≤ e7 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-(-600749 / 3125000)) (-2) (-(-1)) (4152935100111231215521 / 3906250000000000000000) (-(7035413039 / 90864586961)) (by norm_num) (by norm_num)
  have h8 : |(a8 : ℝ) - (r8 : ℝ)| ≤ e8 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991) (by norm_num) (by norm_num)
  have h9 : |(a9 : ℝ) - (r9 : ℝ)| ≤ e9 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-(-15094393 / 100000000)) (-3) (-(-2)) (116121632550302254081 / 78125000000000000000) (-(4750000000 / 9672596991)) (by norm_num) (by norm_num)
  have h10 : |(a10 : ℝ) - (r10 : ℝ)| ≤ e10 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603) (by norm_num) (by norm_num)
  have h11 : |(a11 : ℝ) - (r11 : ℝ)| ≤ e11 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (-(5956127 / 100000000)) (-3) (-(-2)) (44072316385479339890481 / 31250000000000000000000) (-(14662500000 / 68424667603)) (by norm_num) (by norm_num)
  have h12 : |(a12 : ℝ) - (r12 : ℝ)| ≤ e12 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877) (by norm_num) (by norm_num)
  have h13 : |(a13 : ℝ) - (r13 : ℝ)| ≤ e13 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-(-21715849 / 200000000)) (-3) (-(-2)) (17573173268562009901129 / 12207031250000000000000) (-(9920000000 / 132192158877)) (by norm_num) (by norm_num)
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
  change |(manuscriptCase2Y4SubstituteRat : ℝ) - (manuscriptCase2Y4RoundedSubstituteRat : ℝ)| ≤ e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 at hs13
  exact hs13.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case2Y4_actual_substitution_error :
    |barrierCase2Y (Case2PointData.Y4 : ℝ) - (manuscriptCase2Y4SubstituteRat : ℝ)| < ((14 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase2Y4Interval.2 - manuscriptCase2Y4Interval.1 < ((14 / 1000000000000000) : ℚ) :=
    manuscript_case2Y4_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase2Y4Interval.1 manuscriptCase2Y4Interval.2 manuscriptCase2Y4SubstituteRat
    (barrierCase2Y (Case2PointData.Y4 : ℝ)) (14 / 1000000000000000)
    manuscript_case2Y4_interval manuscript_case2Y4_substitute_interval hw

end InternalCatalan

end

end

end OAI

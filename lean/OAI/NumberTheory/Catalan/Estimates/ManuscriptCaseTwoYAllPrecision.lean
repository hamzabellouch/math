import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY8LogPrecisionGroup0
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY8LogPrecisionGroup1
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY8LogPrecisionGroup2
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY9LogPrecisionGroup0
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY9LogPrecisionGroup1
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoY9LogPrecisionGroup2
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY0SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY10SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY11SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY12SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY13SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY14SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY15SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY16SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY17SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY1SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY2SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY3SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY4SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY5SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY6SubstitutionError
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoY7SubstitutionError

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case2PointData

def manuscriptCase2Y8FieldInterval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase2YRat Y8) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000)

theorem manuscriptCase2Y8_field_rounded :
    (-137583678496516185242047990451906526993 / 312500000000000000000000000000000000000) ≤ manuscriptCase2Y8FieldInterval.1 ∧
      manuscriptCase2Y8FieldInterval.2 ≤ (-4402677711888517927323504657380573623919 / 10000000000000000000000000000000000000000) := by
  unfold manuscriptCase2Y8FieldInterval manuscriptYLogFieldInterval barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

private theorem manuscriptCase2Y8_YV_tail_eq :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y8 : ℝ))).sum =
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) +
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) +
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) +
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) +
      barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) := by
  apply barrierV2Tail_paired_sum
  intro i hi
  rw [barrierV2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV5_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV7_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV9_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y8YV11_arg_regular

def manuscriptCase2Y8Interval : ℚ × ℚ :=
  (manuscriptCase2Y8FieldInterval.1 + 1 * manuscriptCase2Y8YV0Interval.1 + 1 * manuscriptCase2Y8YV1Interval.1 + 1 * manuscriptCase2Y8YV2Interval.1 + 1 * manuscriptCase2Y8YV3Interval.1 + 1 * manuscriptCase2Y8YV4Interval.1 + 2 * manuscriptCase2Y8YV5Interval.1 + 2 * manuscriptCase2Y8YV7Interval.1 + 2 * manuscriptCase2Y8YV9Interval.1 + 2 * manuscriptCase2Y8YV11Interval.1,
   manuscriptCase2Y8FieldInterval.2 + 1 * manuscriptCase2Y8YV0Interval.2 + 1 * manuscriptCase2Y8YV1Interval.2 + 1 * manuscriptCase2Y8YV2Interval.2 + 1 * manuscriptCase2Y8YV3Interval.2 + 1 * manuscriptCase2Y8YV4Interval.2 + 2 * manuscriptCase2Y8YV5Interval.2 + 2 * manuscriptCase2Y8YV7Interval.2 + 2 * manuscriptCase2Y8YV9Interval.2 + 2 * manuscriptCase2Y8YV11Interval.2)

theorem manuscript_case2Y8_interval :
    barrierCase2Y (Y8 : ℝ) ∈ Set.Icc (manuscriptCase2Y8Interval.1 : ℝ) (manuscriptCase2Y8Interval.2 : ℝ) := by
  have he := barrierCase2Y_eval_rat Y8 (by norm_num [Y8])
  rw [manuscriptCase2Y8_YV_tail_eq] at he
  have hf := manuscript_y_log_field_interval (barrierCase2YRat Y8)
    (Y8 : ℝ) (1 - (Y8 : ℝ)) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) Y8_normalizations.1 Y8_normalizations.2
  change _ ∈ Set.Icc (manuscriptCase2Y8FieldInterval.1 : ℝ) (manuscriptCase2Y8FieldInterval.2 : ℝ) at hf
  constructor
  · change (manuscriptCase2Y8Interval.1 : ℝ) ≤ _
    dsimp only [manuscriptCase2Y8Interval]
    push_cast
    linarith only [he, hf.1,
      manuscriptCase2Y8YV0_exact_interval.1,
      manuscriptCase2Y8YV1_exact_interval.1,
      manuscriptCase2Y8YV2_exact_interval.1,
      manuscriptCase2Y8YV3_exact_interval.1,
      manuscriptCase2Y8YV4_exact_interval.1,
      manuscriptCase2Y8YV5_exact_interval.1,
      manuscriptCase2Y8YV7_exact_interval.1,
      manuscriptCase2Y8YV9_exact_interval.1,
      manuscriptCase2Y8YV11_exact_interval.1]
  · change _ ≤ (manuscriptCase2Y8Interval.2 : ℝ)
    dsimp only [manuscriptCase2Y8Interval]
    push_cast
    linarith only [he, hf.2,
      manuscriptCase2Y8YV0_exact_interval.2,
      manuscriptCase2Y8YV1_exact_interval.2,
      manuscriptCase2Y8YV2_exact_interval.2,
      manuscriptCase2Y8YV3_exact_interval.2,
      manuscriptCase2Y8YV4_exact_interval.2,
      manuscriptCase2Y8YV5_exact_interval.2,
      manuscriptCase2Y8YV7_exact_interval.2,
      manuscriptCase2Y8YV9_exact_interval.2,
      manuscriptCase2Y8YV11_exact_interval.2]

theorem manuscript_case2Y8_rounded_endpoints :
    (-8044802152390827386849442534754246993667 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y8Interval.1 ∧ manuscriptCase2Y8Interval.2 ≤ (-8044802152390827015628285597875998108771 / 5000000000000000000000000000000000000000) := by
  constructor
  · dsimp only [manuscriptCase2Y8Interval]
    linarith only [manuscriptCase2Y8_field_rounded.1,
      manuscriptCase2Y8YV0_rounded_endpoints.1,
      manuscriptCase2Y8YV1_rounded_endpoints.1,
      manuscriptCase2Y8YV2_rounded_endpoints.1,
      manuscriptCase2Y8YV3_rounded_endpoints.1,
      manuscriptCase2Y8YV4_rounded_endpoints.1,
      manuscriptCase2Y8YV5_rounded_endpoints.1,
      manuscriptCase2Y8YV7_rounded_endpoints.1,
      manuscriptCase2Y8YV9_rounded_endpoints.1,
      manuscriptCase2Y8YV11_rounded_endpoints.1]
  · dsimp only [manuscriptCase2Y8Interval]
    linarith only [manuscriptCase2Y8_field_rounded.2,
      manuscriptCase2Y8YV0_rounded_endpoints.2,
      manuscriptCase2Y8YV1_rounded_endpoints.2,
      manuscriptCase2Y8YV2_rounded_endpoints.2,
      manuscriptCase2Y8YV3_rounded_endpoints.2,
      manuscriptCase2Y8YV4_rounded_endpoints.2,
      manuscriptCase2Y8YV5_rounded_endpoints.2,
      manuscriptCase2Y8YV7_rounded_endpoints.2,
      manuscriptCase2Y8YV9_rounded_endpoints.2,
      manuscriptCase2Y8YV11_rounded_endpoints.2]

def manuscriptCase2Y8PrintedUpper : ℚ := (-804480215239 / 500000000000)

theorem manuscript_case2Y8_endpoint_lt_printed :
    manuscriptCase2Y8Interval.2 < manuscriptCase2Y8PrintedUpper :=
  manuscript_case2Y8_rounded_endpoints.2.trans_lt (by decide +kernel)

theorem manuscript_case2Y8_interval_width :
    manuscriptCase2Y8Interval.2 - manuscriptCase2Y8Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  have hw : (-8044802152390827015628285597875998108771 / 5000000000000000000000000000000000000000) - (-8044802152390827386849442534754246993667 / 5000000000000000000000000000000000000000) < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by decide +kernel
  linarith only [hw, manuscript_case2Y8_rounded_endpoints.1, manuscript_case2Y8_rounded_endpoints.2]

theorem manuscript_case2Y8_printed_upper :
    barrierCase2Y (Y8 : ℝ) < (manuscriptCase2Y8PrintedUpper : ℝ) :=
  manuscript_case2Y8_interval.2.trans_lt ((Rat.cast_lt (K := ℝ)).2 manuscript_case2Y8_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open Case2PointData

def manuscriptCase2Y9FieldInterval : ℚ × ℚ :=
  manuscriptYLogFieldInterval (barrierCase2YRat Y9) (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000)

theorem manuscriptCase2Y9_field_rounded :
    (-2315871056313392082706586299692795883943 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y9FieldInterval.1 ∧
      manuscriptCase2Y9FieldInterval.2 ≤ (-2315871056313392082439299803255108153737 / 5000000000000000000000000000000000000000) := by
  unfold manuscriptCase2Y9FieldInterval manuscriptYLogFieldInterval barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

private theorem manuscriptCase2Y9_YV_tail_eq :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y9 : ℝ))).sum =
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) +
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) +
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) +
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) +
      barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) +
      2 * barrierCase2YVLogTerm (Y9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) := by
  apply barrierV2Tail_paired_sum
  intro i hi
  rw [barrierV2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV5_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV7_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV9_arg_regular
  · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y9YV11_arg_regular

def manuscriptCase2Y9Interval : ℚ × ℚ :=
  (manuscriptCase2Y9FieldInterval.1 + 1 * manuscriptCase2Y9YV0Interval.1 + 1 * manuscriptCase2Y9YV1Interval.1 + 1 * manuscriptCase2Y9YV2Interval.1 + 1 * manuscriptCase2Y9YV3Interval.1 + 1 * manuscriptCase2Y9YV4Interval.1 + 2 * manuscriptCase2Y9YV5Interval.1 + 2 * manuscriptCase2Y9YV7Interval.1 + 2 * manuscriptCase2Y9YV9Interval.1 + 2 * manuscriptCase2Y9YV11Interval.1,
   manuscriptCase2Y9FieldInterval.2 + 1 * manuscriptCase2Y9YV0Interval.2 + 1 * manuscriptCase2Y9YV1Interval.2 + 1 * manuscriptCase2Y9YV2Interval.2 + 1 * manuscriptCase2Y9YV3Interval.2 + 1 * manuscriptCase2Y9YV4Interval.2 + 2 * manuscriptCase2Y9YV5Interval.2 + 2 * manuscriptCase2Y9YV7Interval.2 + 2 * manuscriptCase2Y9YV9Interval.2 + 2 * manuscriptCase2Y9YV11Interval.2)

theorem manuscript_case2Y9_interval :
    barrierCase2Y (Y9 : ℝ) ∈ Set.Icc (manuscriptCase2Y9Interval.1 : ℝ) (manuscriptCase2Y9Interval.2 : ℝ) := by
  have he := barrierCase2Y_eval_rat Y9 (by norm_num [Y9])
  rw [manuscriptCase2Y9_YV_tail_eq] at he
  have hf := manuscript_y_log_field_interval (barrierCase2YRat Y9)
    (Y9 : ℝ) (1 - (Y9 : ℝ)) (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000) Y9_normalizations.1 Y9_normalizations.2
  change _ ∈ Set.Icc (manuscriptCase2Y9FieldInterval.1 : ℝ) (manuscriptCase2Y9FieldInterval.2 : ℝ) at hf
  constructor
  · change (manuscriptCase2Y9Interval.1 : ℝ) ≤ _
    dsimp only [manuscriptCase2Y9Interval]
    push_cast
    linarith only [he, hf.1,
      manuscriptCase2Y9YV0_exact_interval.1,
      manuscriptCase2Y9YV1_exact_interval.1,
      manuscriptCase2Y9YV2_exact_interval.1,
      manuscriptCase2Y9YV3_exact_interval.1,
      manuscriptCase2Y9YV4_exact_interval.1,
      manuscriptCase2Y9YV5_exact_interval.1,
      manuscriptCase2Y9YV7_exact_interval.1,
      manuscriptCase2Y9YV9_exact_interval.1,
      manuscriptCase2Y9YV11_exact_interval.1]
  · change _ ≤ (manuscriptCase2Y9Interval.2 : ℝ)
    dsimp only [manuscriptCase2Y9Interval]
    push_cast
    linarith only [he, hf.2,
      manuscriptCase2Y9YV0_exact_interval.2,
      manuscriptCase2Y9YV1_exact_interval.2,
      manuscriptCase2Y9YV2_exact_interval.2,
      manuscriptCase2Y9YV3_exact_interval.2,
      manuscriptCase2Y9YV4_exact_interval.2,
      manuscriptCase2Y9YV5_exact_interval.2,
      manuscriptCase2Y9YV7_exact_interval.2,
      manuscriptCase2Y9YV9_exact_interval.2,
      manuscriptCase2Y9YV11_exact_interval.2]

theorem manuscript_case2Y9_rounded_endpoints :
    (-3217981097625407675790755583809848633173 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y9Interval.1 ∧ manuscriptCase2Y9Interval.2 ≤ (-16089905488127037635898962235099380679937 / 10000000000000000000000000000000000000000) := by
  constructor
  · dsimp only [manuscriptCase2Y9Interval]
    linarith only [manuscriptCase2Y9_field_rounded.1,
      manuscriptCase2Y9YV0_rounded_endpoints.1,
      manuscriptCase2Y9YV1_rounded_endpoints.1,
      manuscriptCase2Y9YV2_rounded_endpoints.1,
      manuscriptCase2Y9YV3_rounded_endpoints.1,
      manuscriptCase2Y9YV4_rounded_endpoints.1,
      manuscriptCase2Y9YV5_rounded_endpoints.1,
      manuscriptCase2Y9YV7_rounded_endpoints.1,
      manuscriptCase2Y9YV9_rounded_endpoints.1,
      manuscriptCase2Y9YV11_rounded_endpoints.1]
  · dsimp only [manuscriptCase2Y9Interval]
    linarith only [manuscriptCase2Y9_field_rounded.2,
      manuscriptCase2Y9YV0_rounded_endpoints.2,
      manuscriptCase2Y9YV1_rounded_endpoints.2,
      manuscriptCase2Y9YV2_rounded_endpoints.2,
      manuscriptCase2Y9YV3_rounded_endpoints.2,
      manuscriptCase2Y9YV4_rounded_endpoints.2,
      manuscriptCase2Y9YV5_rounded_endpoints.2,
      manuscriptCase2Y9YV7_rounded_endpoints.2,
      manuscriptCase2Y9YV9_rounded_endpoints.2,
      manuscriptCase2Y9YV11_rounded_endpoints.2]

def manuscriptCase2Y9PrintedUpper : ℚ := (-402247637203 / 250000000000)

theorem manuscript_case2Y9_endpoint_lt_printed :
    manuscriptCase2Y9Interval.2 < manuscriptCase2Y9PrintedUpper :=
  manuscript_case2Y9_rounded_endpoints.2.trans_lt (by decide +kernel)

theorem manuscript_case2Y9_interval_width :
    manuscriptCase2Y9Interval.2 - manuscriptCase2Y9Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  have hw : (-16089905488127037635898962235099380679937 / 10000000000000000000000000000000000000000) - (-3217981097625407675790755583809848633173 / 2000000000000000000000000000000000000000) < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by decide +kernel
  linarith only [hw, manuscript_case2Y9_rounded_endpoints.1, manuscript_case2Y9_rounded_endpoints.2]

theorem manuscript_case2Y9_printed_upper :
    barrierCase2Y (Y9 : ℝ) < (manuscriptCase2Y9PrintedUpper : ℝ) :=
  manuscript_case2Y9_interval.2.trans_lt ((Rat.cast_lt (K := ℝ)).2 manuscript_case2Y9_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y8SubstituteRat : ℚ :=
  barrierCase2YApproxRat Case2PointData.Y8 (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) +
    (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (79955365900021143329209 / 62500000000000000000000) (-(97900000000 / 265275245547))) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357)) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (0) (-(-2)) (3837815698817694023449 / 2500000000000000000000) (-(9500000000 / 61217364357))) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081)) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (0) (-(-2)) (1695578418632015995919049 / 1000000000000000000000000) (-(29325000000 / 433056170081))) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879)) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (0) (-(-2)) (700355618901393739268641 / 390625000000000000000000) (-(19840000000 / 836637312879)))

theorem manuscript_case2Y8_substitute_interval :
    manuscriptCase2Y8SubstituteRat ∈ Set.Icc manuscriptCase2Y8Interval.1 manuscriptCase2Y8Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase2YRat Case2PointData.Y8) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) (by norm_num) (by norm_num)
  change (barrierCase2YApproxRat Case2PointData.Y8 (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000)) ∈ Set.Icc manuscriptCase2Y8FieldInterval.1 manuscriptCase2Y8FieldInterval.2 at hf
  have ht0 := manuscript_weightedComplexLogRat_interval (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y8YV0Interval.1 manuscriptCase2Y8YV0Interval.2 at ht0
  have ht1 := manuscript_weightedComplexLogRat_interval (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y8YV1Interval.1 manuscriptCase2Y8YV1Interval.2 at ht1
  have ht2 := manuscript_weightedComplexLogRat_interval (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y8YV2Interval.1 manuscriptCase2Y8YV2Interval.2 at ht2
  have ht3 := manuscript_weightedComplexLogRat_interval (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y8YV3Interval.1 manuscriptCase2Y8YV3Interval.2 at ht3
  have ht4 := manuscript_weightedComplexLogRat_interval (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y8YV4Interval.1 manuscriptCase2Y8YV4Interval.2 at ht4
  have ht5 := manuscript_weightedComplexLogRat_interval (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547) (by norm_num)
  change (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547)) ∈ Set.Icc manuscriptCase2Y8YV5Interval.1 manuscriptCase2Y8YV5Interval.2 at ht5
  have hc5 := manuscript_weightedComplexLogRat_conj (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547)
  have ht6 := manuscript_weightedComplexLogRat_interval (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357) (by norm_num)
  change (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357)) ∈ Set.Icc manuscriptCase2Y8YV7Interval.1 manuscriptCase2Y8YV7Interval.2 at ht6
  have hc6 := manuscript_weightedComplexLogRat_conj (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357)
  have ht7 := manuscript_weightedComplexLogRat_interval (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081) (by norm_num)
  change (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081)) ∈ Set.Icc manuscriptCase2Y8YV9Interval.1 manuscriptCase2Y8YV9Interval.2 at ht7
  have hc7 := manuscript_weightedComplexLogRat_conj (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081)
  have ht8 := manuscript_weightedComplexLogRat_interval (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879) (by norm_num)
  change (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879)) ∈ Set.Icc manuscriptCase2Y8YV11Interval.1 manuscriptCase2Y8YV11Interval.2 at ht8
  have hc8 := manuscript_weightedComplexLogRat_conj (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879)
  constructor
  · change manuscriptCase2Y8Interval.1 ≤ manuscriptCase2Y8SubstituteRat
    dsimp only [manuscriptCase2Y8Interval, manuscriptCase2Y8SubstituteRat]
    linarith only [hf.1, ht0.1, ht1.1, ht2.1, ht3.1, ht4.1, ht5.1, ht6.1, ht7.1, ht8.1, hc5, hc6, hc7, hc8]
  · change manuscriptCase2Y8SubstituteRat ≤ manuscriptCase2Y8Interval.2
    dsimp only [manuscriptCase2Y8Interval, manuscriptCase2Y8SubstituteRat]
    linarith only [hf.2, ht0.2, ht1.2, ht2.2, ht3.2, ht4.2, ht5.2, ht6.2, ht7.2, ht8.2, hc5, hc6, hc7, hc8]

theorem manuscript_case2Y8_substitute_cutoff :
    manuscriptCase2Y8SubstituteRat < ((-160891 / 100000) : ℚ) := by
  have hp : manuscriptCase2Y8PrintedUpper < ((-160891 / 100000) : ℚ) := by norm_num [manuscriptCase2Y8PrintedUpper]
  exact manuscript_case2Y8_substitute_interval.2.trans_lt (manuscript_case2Y8_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y9SubstituteRat : ℚ :=
  barrierCase2YApproxRat Case2PointData.Y9 (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000) +
    (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679)) +
    (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (107708435368848314367961 / 62500000000000000000000) (-(8900000000 / 28477049679))) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339)) +
    (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (1) (-(-2)) (5315789812542217924921 / 5000000000000000000000) (-(9500000000 / 72287895339))) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287)) +
    (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (1) (-(-2)) (2361232414221946322457321 / 2000000000000000000000000) (-(29325000000 / 511369926287))) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633)) +
    (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (1) (-(-2)) (976408339475940925754689 / 781250000000000000000000) (-(19840000000 / 987934569633)))

theorem manuscript_case2Y9_substitute_interval :
    manuscriptCase2Y9SubstituteRat ∈ Set.Icc manuscriptCase2Y9Interval.1 manuscriptCase2Y9Interval.2 := by
  have hf := manuscript_y_substitute_interval (barrierCase2YRat Case2PointData.Y9) (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000) (by norm_num) (by norm_num)
  change (barrierCase2YApproxRat Case2PointData.Y9 (-1) (-3) (8031988371 / 5000000000) (1968011629 / 1250000000)) ∈ Set.Icc manuscriptCase2Y9FieldInterval.1 manuscriptCase2Y9FieldInterval.2 at hf
  have ht0 := manuscript_weightedComplexLogRat_interval (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y9YV0Interval.1 manuscriptCase2Y9YV0Interval.2 at ht0
  have ht1 := manuscript_weightedComplexLogRat_interval (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y9YV1Interval.1 manuscriptCase2Y9YV1Interval.2 at ht1
  have ht2 := manuscript_weightedComplexLogRat_interval (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y9YV2Interval.1 manuscriptCase2Y9YV2Interval.2 at ht2
  have ht3 := manuscript_weightedComplexLogRat_interval (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (1416936798123903344401 / 1250000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y9YV3Interval.1 manuscriptCase2Y9YV3Interval.2 at ht3
  have ht4 := manuscript_weightedComplexLogRat_interval (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (58673159116478365754689 / 48828125000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2Y9YV4Interval.1 manuscriptCase2Y9YV4Interval.2 at ht4
  have ht5 := manuscript_weightedComplexLogRat_interval (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679) (by norm_num)
  change (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679)) ∈ Set.Icc manuscriptCase2Y9YV5Interval.1 manuscriptCase2Y9YV5Interval.2 at ht5
  have hc5 := manuscript_weightedComplexLogRat_conj (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (107708435368848314367961 / 62500000000000000000000) (8900000000 / 28477049679)
  have ht6 := manuscript_weightedComplexLogRat_interval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339) (by norm_num)
  change (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339)) ∈ Set.Icc manuscriptCase2Y9YV7Interval.1 manuscriptCase2Y9YV7Interval.2 at ht6
  have hc6 := manuscript_weightedComplexLogRat_conj (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339)
  have ht7 := manuscript_weightedComplexLogRat_interval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287) (by norm_num)
  change (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287)) ∈ Set.Icc manuscriptCase2Y9YV9Interval.1 manuscriptCase2Y9YV9Interval.2 at ht7
  have hc7 := manuscript_weightedComplexLogRat_conj (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287)
  have ht8 := manuscript_weightedComplexLogRat_interval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633) (by norm_num)
  change (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633)) ∈ Set.Icc manuscriptCase2Y9YV11Interval.1 manuscriptCase2Y9YV11Interval.2 at ht8
  have hc8 := manuscript_weightedComplexLogRat_conj (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633)
  constructor
  · change manuscriptCase2Y9Interval.1 ≤ manuscriptCase2Y9SubstituteRat
    dsimp only [manuscriptCase2Y9Interval, manuscriptCase2Y9SubstituteRat]
    linarith only [hf.1, ht0.1, ht1.1, ht2.1, ht3.1, ht4.1, ht5.1, ht6.1, ht7.1, ht8.1, hc5, hc6, hc7, hc8]
  · change manuscriptCase2Y9SubstituteRat ≤ manuscriptCase2Y9Interval.2
    dsimp only [manuscriptCase2Y9Interval, manuscriptCase2Y9SubstituteRat]
    linarith only [hf.2, ht0.2, ht1.2, ht2.2, ht3.2, ht4.2, ht5.2, ht6.2, ht7.2, ht8.2, hc5, hc6, hc7, hc8]

theorem manuscript_case2Y9_substitute_cutoff :
    manuscriptCase2Y9SubstituteRat < ((-160891 / 100000) : ℚ) := by
  have hp : manuscriptCase2Y9PrintedUpper < ((-160891 / 100000) : ℚ) := by norm_num [manuscriptCase2Y9PrintedUpper]
  exact manuscript_case2Y9_substitute_interval.2.trans_lt (manuscript_case2Y9_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptCase2YPrecisionClaims : Prop :=
  (barrierCase2Y (Case2PointData.Y0 : ℝ) ∈ Set.Icc (manuscriptCase2Y0Interval.1 : ℝ) (manuscriptCase2Y0Interval.2 : ℝ) ∧
    manuscriptCase2Y0Interval.2 < manuscriptCase2Y0PrintedUpper ∧
    manuscriptCase2Y0Interval.2 - manuscriptCase2Y0Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y0 : ℝ) < (manuscriptCase2Y0PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y1 : ℝ) ∈ Set.Icc (manuscriptCase2Y1Interval.1 : ℝ) (manuscriptCase2Y1Interval.2 : ℝ) ∧
    manuscriptCase2Y1Interval.2 < manuscriptCase2Y1PrintedUpper ∧
    manuscriptCase2Y1Interval.2 - manuscriptCase2Y1Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y1 : ℝ) < (manuscriptCase2Y1PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y2 : ℝ) ∈ Set.Icc (manuscriptCase2Y2Interval.1 : ℝ) (manuscriptCase2Y2Interval.2 : ℝ) ∧
    manuscriptCase2Y2Interval.2 < manuscriptCase2Y2PrintedUpper ∧
    manuscriptCase2Y2Interval.2 - manuscriptCase2Y2Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y2 : ℝ) < (manuscriptCase2Y2PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y3 : ℝ) ∈ Set.Icc (manuscriptCase2Y3Interval.1 : ℝ) (manuscriptCase2Y3Interval.2 : ℝ) ∧
    manuscriptCase2Y3Interval.2 < manuscriptCase2Y3PrintedUpper ∧
    manuscriptCase2Y3Interval.2 - manuscriptCase2Y3Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y3 : ℝ) < (manuscriptCase2Y3PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y4 : ℝ) ∈ Set.Icc (manuscriptCase2Y4Interval.1 : ℝ) (manuscriptCase2Y4Interval.2 : ℝ) ∧
    manuscriptCase2Y4Interval.2 < manuscriptCase2Y4PrintedUpper ∧
    manuscriptCase2Y4Interval.2 - manuscriptCase2Y4Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y4 : ℝ) < (manuscriptCase2Y4PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y5 : ℝ) ∈ Set.Icc (manuscriptCase2Y5Interval.1 : ℝ) (manuscriptCase2Y5Interval.2 : ℝ) ∧
    manuscriptCase2Y5Interval.2 < manuscriptCase2Y5PrintedUpper ∧
    manuscriptCase2Y5Interval.2 - manuscriptCase2Y5Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y5 : ℝ) < (manuscriptCase2Y5PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y6 : ℝ) ∈ Set.Icc (manuscriptCase2Y6Interval.1 : ℝ) (manuscriptCase2Y6Interval.2 : ℝ) ∧
    manuscriptCase2Y6Interval.2 < manuscriptCase2Y6PrintedUpper ∧
    manuscriptCase2Y6Interval.2 - manuscriptCase2Y6Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y6 : ℝ) < (manuscriptCase2Y6PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y7 : ℝ) ∈ Set.Icc (manuscriptCase2Y7Interval.1 : ℝ) (manuscriptCase2Y7Interval.2 : ℝ) ∧
    manuscriptCase2Y7Interval.2 < manuscriptCase2Y7PrintedUpper ∧
    manuscriptCase2Y7Interval.2 - manuscriptCase2Y7Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y7 : ℝ) < (manuscriptCase2Y7PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y8 : ℝ) ∈ Set.Icc (manuscriptCase2Y8Interval.1 : ℝ) (manuscriptCase2Y8Interval.2 : ℝ) ∧
    manuscriptCase2Y8Interval.2 < manuscriptCase2Y8PrintedUpper ∧
    manuscriptCase2Y8Interval.2 - manuscriptCase2Y8Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y8 : ℝ) < (manuscriptCase2Y8PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y9 : ℝ) ∈ Set.Icc (manuscriptCase2Y9Interval.1 : ℝ) (manuscriptCase2Y9Interval.2 : ℝ) ∧
    manuscriptCase2Y9Interval.2 < manuscriptCase2Y9PrintedUpper ∧
    manuscriptCase2Y9Interval.2 - manuscriptCase2Y9Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y9 : ℝ) < (manuscriptCase2Y9PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y10 : ℝ) ∈ Set.Icc (manuscriptCase2Y10Interval.1 : ℝ) (manuscriptCase2Y10Interval.2 : ℝ) ∧
    manuscriptCase2Y10Interval.2 < manuscriptCase2Y10PrintedUpper ∧
    manuscriptCase2Y10Interval.2 - manuscriptCase2Y10Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y10 : ℝ) < (manuscriptCase2Y10PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y11 : ℝ) ∈ Set.Icc (manuscriptCase2Y11Interval.1 : ℝ) (manuscriptCase2Y11Interval.2 : ℝ) ∧
    manuscriptCase2Y11Interval.2 < manuscriptCase2Y11PrintedUpper ∧
    manuscriptCase2Y11Interval.2 - manuscriptCase2Y11Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y11 : ℝ) < (manuscriptCase2Y11PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y12 : ℝ) ∈ Set.Icc (manuscriptCase2Y12Interval.1 : ℝ) (manuscriptCase2Y12Interval.2 : ℝ) ∧
    manuscriptCase2Y12Interval.2 < manuscriptCase2Y12PrintedUpper ∧
    manuscriptCase2Y12Interval.2 - manuscriptCase2Y12Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y12 : ℝ) < (manuscriptCase2Y12PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y13 : ℝ) ∈ Set.Icc (manuscriptCase2Y13Interval.1 : ℝ) (manuscriptCase2Y13Interval.2 : ℝ) ∧
    manuscriptCase2Y13Interval.2 < manuscriptCase2Y13PrintedUpper ∧
    manuscriptCase2Y13Interval.2 - manuscriptCase2Y13Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y13 : ℝ) < (manuscriptCase2Y13PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y14 : ℝ) ∈ Set.Icc (manuscriptCase2Y14Interval.1 : ℝ) (manuscriptCase2Y14Interval.2 : ℝ) ∧
    manuscriptCase2Y14Interval.2 < manuscriptCase2Y14PrintedUpper ∧
    manuscriptCase2Y14Interval.2 - manuscriptCase2Y14Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y14 : ℝ) < (manuscriptCase2Y14PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y15 : ℝ) ∈ Set.Icc (manuscriptCase2Y15Interval.1 : ℝ) (manuscriptCase2Y15Interval.2 : ℝ) ∧
    manuscriptCase2Y15Interval.2 < manuscriptCase2Y15PrintedUpper ∧
    manuscriptCase2Y15Interval.2 - manuscriptCase2Y15Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y15 : ℝ) < (manuscriptCase2Y15PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y16 : ℝ) ∈ Set.Icc (manuscriptCase2Y16Interval.1 : ℝ) (manuscriptCase2Y16Interval.2 : ℝ) ∧
    manuscriptCase2Y16Interval.2 < manuscriptCase2Y16PrintedUpper ∧
    manuscriptCase2Y16Interval.2 - manuscriptCase2Y16Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y16 : ℝ) < (manuscriptCase2Y16PrintedUpper : ℝ)) ∧
  (barrierCase2Y (Case2PointData.Y17 : ℝ) ∈ Set.Icc (manuscriptCase2Y17Interval.1 : ℝ) (manuscriptCase2Y17Interval.2 : ℝ) ∧
    manuscriptCase2Y17Interval.2 < manuscriptCase2Y17PrintedUpper ∧
    manuscriptCase2Y17Interval.2 - manuscriptCase2Y17Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) ∧
    barrierCase2Y (Case2PointData.Y17 : ℝ) < (manuscriptCase2Y17PrintedUpper : ℝ))

theorem manuscript_case2Y_all_precision : manuscriptCase2YPrecisionClaims := by
  exact ⟨⟨manuscript_case2Y0_interval, manuscript_case2Y0_endpoint_lt_printed, manuscript_case2Y0_interval_width, manuscript_case2Y0_printed_upper⟩,
    ⟨manuscript_case2Y1_interval, manuscript_case2Y1_endpoint_lt_printed, manuscript_case2Y1_interval_width, manuscript_case2Y1_printed_upper⟩,
    ⟨manuscript_case2Y2_interval, manuscript_case2Y2_endpoint_lt_printed, manuscript_case2Y2_interval_width, manuscript_case2Y2_printed_upper⟩,
    ⟨manuscript_case2Y3_interval, manuscript_case2Y3_endpoint_lt_printed, manuscript_case2Y3_interval_width, manuscript_case2Y3_printed_upper⟩,
    ⟨manuscript_case2Y4_interval, manuscript_case2Y4_endpoint_lt_printed, manuscript_case2Y4_interval_width, manuscript_case2Y4_printed_upper⟩,
    ⟨manuscript_case2Y5_interval, manuscript_case2Y5_endpoint_lt_printed, manuscript_case2Y5_interval_width, manuscript_case2Y5_printed_upper⟩,
    ⟨manuscript_case2Y6_interval, manuscript_case2Y6_endpoint_lt_printed, manuscript_case2Y6_interval_width, manuscript_case2Y6_printed_upper⟩,
    ⟨manuscript_case2Y7_interval, manuscript_case2Y7_endpoint_lt_printed, manuscript_case2Y7_interval_width, manuscript_case2Y7_printed_upper⟩,
    ⟨manuscript_case2Y8_interval, manuscript_case2Y8_endpoint_lt_printed, manuscript_case2Y8_interval_width, manuscript_case2Y8_printed_upper⟩,
    ⟨manuscript_case2Y9_interval, manuscript_case2Y9_endpoint_lt_printed, manuscript_case2Y9_interval_width, manuscript_case2Y9_printed_upper⟩,
    ⟨manuscript_case2Y10_interval, manuscript_case2Y10_endpoint_lt_printed, manuscript_case2Y10_interval_width, manuscript_case2Y10_printed_upper⟩,
    ⟨manuscript_case2Y11_interval, manuscript_case2Y11_endpoint_lt_printed, manuscript_case2Y11_interval_width, manuscript_case2Y11_printed_upper⟩,
    ⟨manuscript_case2Y12_interval, manuscript_case2Y12_endpoint_lt_printed, manuscript_case2Y12_interval_width, manuscript_case2Y12_printed_upper⟩,
    ⟨manuscript_case2Y13_interval, manuscript_case2Y13_endpoint_lt_printed, manuscript_case2Y13_interval_width, manuscript_case2Y13_printed_upper⟩,
    ⟨manuscript_case2Y14_interval, manuscript_case2Y14_endpoint_lt_printed, manuscript_case2Y14_interval_width, manuscript_case2Y14_printed_upper⟩,
    ⟨manuscript_case2Y15_interval, manuscript_case2Y15_endpoint_lt_printed, manuscript_case2Y15_interval_width, manuscript_case2Y15_printed_upper⟩,
    ⟨manuscript_case2Y16_interval, manuscript_case2Y16_endpoint_lt_printed, manuscript_case2Y16_interval_width, manuscript_case2Y16_printed_upper⟩,
    ⟨manuscript_case2Y17_interval, manuscript_case2Y17_endpoint_lt_printed, manuscript_case2Y17_interval_width, manuscript_case2Y17_printed_upper⟩⟩

end InternalCatalan

end

end

end OAI

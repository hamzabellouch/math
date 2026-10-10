import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoX11LogPrecisionGroup0
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoX11LogPrecisionGroup1
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoX11LogPrecisionGroup2
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoX11LogPrecisionGroup3
import OAI.NumberTheory.Catalan.Analysis.ManuscriptCaseTwoX11LogPrecisionGroup4
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4PointRounding

namespace OAI

section

noncomputable section
namespace InternalCatalan
open Case2PointData

def manuscriptCase2X11FieldInterval : ℚ × ℚ :=
  manuscriptXLogFieldInterval (65 / 48) (barrierCase2XRat X11) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000)

theorem manuscriptCase2X11_field_rounded :
    (-10360036644627201438955097783380683515453 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X11FieldInterval.1 ∧
      manuscriptCase2X11FieldInterval.2 ≤ (-10360036644627201438364254331468133267119 / 5000000000000000000000000000000000000000) := by
  unfold manuscriptCase2X11FieldInterval manuscriptXLogFieldInterval barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, barrierLogHRat_two_eq]
  decide +kernel

private theorem manuscriptCase2X11_XP_tail_eq :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X11 : ℝ))).sum =
      barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 0 (0, 0)) +
      barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 1 (0, 0)) +
      2 * barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 2 (0, 0)) +
      2 * barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 4 (0, 0)) +
      2 * barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 6 (0, 0)) +
      2 * barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD 8 (0, 0)) := by
  apply barrierP2Tail_paired_sum
  intro i hi
  rw [barrierP2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP2_arg_regular
  · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP4_arg_regular
  · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP6_arg_regular
  · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP8_arg_regular

private theorem manuscriptCase2X11_XV_tail_eq :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X11 : ℝ))).sum =
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) +
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) +
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) +
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) +
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) +
      2 * barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) +
      2 * barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) +
      2 * barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) +
      2 * barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) := by
  apply barrierV2Tail_paired_sum
  intro i hi
  rw [barrierV2Tail_getD_pair i hi]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV5_arg_regular
  · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV7_arg_regular
  · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV9_arg_regular
  · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV11_arg_regular

def manuscriptCase2X11Interval : ℚ × ℚ :=
  (manuscriptCase2X11FieldInterval.1 + 1 * manuscriptCase2X11XP0Interval.1 + 1 * manuscriptCase2X11XP1Interval.1 + 2 * manuscriptCase2X11XP2Interval.1 + 2 * manuscriptCase2X11XP4Interval.1 + 2 * manuscriptCase2X11XP6Interval.1 + 2 * manuscriptCase2X11XP8Interval.1 + 1 * manuscriptCase2X11XV0Interval.1 + 1 * manuscriptCase2X11XV1Interval.1 + 1 * manuscriptCase2X11XV2Interval.1 + 1 * manuscriptCase2X11XV3Interval.1 + 1 * manuscriptCase2X11XV4Interval.1 + 2 * manuscriptCase2X11XV5Interval.1 + 2 * manuscriptCase2X11XV7Interval.1 + 2 * manuscriptCase2X11XV9Interval.1 + 2 * manuscriptCase2X11XV11Interval.1,
   manuscriptCase2X11FieldInterval.2 + 1 * manuscriptCase2X11XP0Interval.2 + 1 * manuscriptCase2X11XP1Interval.2 + 2 * manuscriptCase2X11XP2Interval.2 + 2 * manuscriptCase2X11XP4Interval.2 + 2 * manuscriptCase2X11XP6Interval.2 + 2 * manuscriptCase2X11XP8Interval.2 + 1 * manuscriptCase2X11XV0Interval.2 + 1 * manuscriptCase2X11XV1Interval.2 + 1 * manuscriptCase2X11XV2Interval.2 + 1 * manuscriptCase2X11XV3Interval.2 + 1 * manuscriptCase2X11XV4Interval.2 + 2 * manuscriptCase2X11XV5Interval.2 + 2 * manuscriptCase2X11XV7Interval.2 + 2 * manuscriptCase2X11XV9Interval.2 + 2 * manuscriptCase2X11XV11Interval.2)

theorem manuscript_case2X11_interval :
    barrierCase2X (X11 : ℝ) ∈ Set.Icc (manuscriptCase2X11Interval.1 : ℝ) (manuscriptCase2X11Interval.2 : ℝ) := by
  have he := barrierCase2X_eval_rat X11 (by norm_num [X11])
  rw [manuscriptCase2X11_XP_tail_eq, manuscriptCase2X11_XV_tail_eq] at he
  have hf := manuscript_x_log_field_interval (65 / 48) (barrierCase2XRat X11)
    |( X11 : ℝ)| (1 - (X11 : ℝ)) (1 + (X11 : ℝ) ^ 2) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) X11_normalizations.1 X11_normalizations.2.1 X11_normalizations.2.2
  change _ ∈ Set.Icc (manuscriptCase2X11FieldInterval.1 : ℝ) (manuscriptCase2X11FieldInterval.2 : ℝ) at hf
  simp only [Rat.cast_div, Rat.cast_ofNat] at hf
  constructor
  · change (manuscriptCase2X11Interval.1 : ℝ) ≤ _
    dsimp only [manuscriptCase2X11Interval]
    push_cast
    linarith only [he, hf.1,
      manuscriptCase2X11XP0_exact_interval.1,
      manuscriptCase2X11XP1_exact_interval.1,
      manuscriptCase2X11XP2_exact_interval.1,
      manuscriptCase2X11XP4_exact_interval.1,
      manuscriptCase2X11XP6_exact_interval.1,
      manuscriptCase2X11XP8_exact_interval.1,
      manuscriptCase2X11XV0_exact_interval.1,
      manuscriptCase2X11XV1_exact_interval.1,
      manuscriptCase2X11XV2_exact_interval.1,
      manuscriptCase2X11XV3_exact_interval.1,
      manuscriptCase2X11XV4_exact_interval.1,
      manuscriptCase2X11XV5_exact_interval.1,
      manuscriptCase2X11XV7_exact_interval.1,
      manuscriptCase2X11XV9_exact_interval.1,
      manuscriptCase2X11XV11_exact_interval.1]
  · change _ ≤ (manuscriptCase2X11Interval.2 : ℝ)
    dsimp only [manuscriptCase2X11Interval]
    push_cast
    linarith only [he, hf.2,
      manuscriptCase2X11XP0_exact_interval.2,
      manuscriptCase2X11XP1_exact_interval.2,
      manuscriptCase2X11XP2_exact_interval.2,
      manuscriptCase2X11XP4_exact_interval.2,
      manuscriptCase2X11XP6_exact_interval.2,
      manuscriptCase2X11XP8_exact_interval.2,
      manuscriptCase2X11XV0_exact_interval.2,
      manuscriptCase2X11XV1_exact_interval.2,
      manuscriptCase2X11XV2_exact_interval.2,
      manuscriptCase2X11XV3_exact_interval.2,
      manuscriptCase2X11XV4_exact_interval.2,
      manuscriptCase2X11XV5_exact_interval.2,
      manuscriptCase2X11XV7_exact_interval.2,
      manuscriptCase2X11XV9_exact_interval.2,
      manuscriptCase2X11XV11_exact_interval.2]

theorem manuscript_case2X11_rounded_endpoints :
    (-9840340268987450088649031370598216934307 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11Interval.1 ∧ manuscriptCase2X11Interval.2 ≤ (-9840340268987449549058181422394523672419 / 10000000000000000000000000000000000000000) := by
  constructor
  · dsimp only [manuscriptCase2X11Interval]
    linarith only [manuscriptCase2X11_field_rounded.1,
      manuscriptCase2X11XP0_rounded_endpoints.1,
      manuscriptCase2X11XP1_rounded_endpoints.1,
      manuscriptCase2X11XP2_rounded_endpoints.1,
      manuscriptCase2X11XP4_rounded_endpoints.1,
      manuscriptCase2X11XP6_rounded_endpoints.1,
      manuscriptCase2X11XP8_rounded_endpoints.1,
      manuscriptCase2X11XV0_rounded_endpoints.1,
      manuscriptCase2X11XV1_rounded_endpoints.1,
      manuscriptCase2X11XV2_rounded_endpoints.1,
      manuscriptCase2X11XV3_rounded_endpoints.1,
      manuscriptCase2X11XV4_rounded_endpoints.1,
      manuscriptCase2X11XV5_rounded_endpoints.1,
      manuscriptCase2X11XV7_rounded_endpoints.1,
      manuscriptCase2X11XV9_rounded_endpoints.1,
      manuscriptCase2X11XV11_rounded_endpoints.1]
  · dsimp only [manuscriptCase2X11Interval]
    linarith only [manuscriptCase2X11_field_rounded.2,
      manuscriptCase2X11XP0_rounded_endpoints.2,
      manuscriptCase2X11XP1_rounded_endpoints.2,
      manuscriptCase2X11XP2_rounded_endpoints.2,
      manuscriptCase2X11XP4_rounded_endpoints.2,
      manuscriptCase2X11XP6_rounded_endpoints.2,
      manuscriptCase2X11XP8_rounded_endpoints.2,
      manuscriptCase2X11XV0_rounded_endpoints.2,
      manuscriptCase2X11XV1_rounded_endpoints.2,
      manuscriptCase2X11XV2_rounded_endpoints.2,
      manuscriptCase2X11XV3_rounded_endpoints.2,
      manuscriptCase2X11XV4_rounded_endpoints.2,
      manuscriptCase2X11XV5_rounded_endpoints.2,
      manuscriptCase2X11XV7_rounded_endpoints.2,
      manuscriptCase2X11XV9_rounded_endpoints.2,
      manuscriptCase2X11XV11_rounded_endpoints.2]

def manuscriptCase2X11PrintedUpper : ℚ := (-492017013449 / 500000000000)

theorem manuscript_case2X11_endpoint_lt_printed :
    manuscriptCase2X11Interval.2 < manuscriptCase2X11PrintedUpper :=
  manuscript_case2X11_rounded_endpoints.2.trans_lt (by decide +kernel)

theorem manuscript_case2X11_interval_width :
    manuscriptCase2X11Interval.2 - manuscriptCase2X11Interval.1 < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by
  have hw : (-9840340268987449549058181422394523672419 / 10000000000000000000000000000000000000000) - (-9840340268987450088649031370598216934307 / 10000000000000000000000000000000000000000) < (216146856249281 / 1000000000000000000000000000000 : ℚ) := by decide +kernel
  linarith only [hw, manuscript_case2X11_rounded_endpoints.1, manuscript_case2X11_rounded_endpoints.2]

theorem manuscript_case2X11_printed_upper :
    barrierCase2X (X11 : ℝ) < (manuscriptCase2X11PrintedUpper : ℝ) :=
  manuscript_case2X11_interval.2.trans_lt ((Rat.cast_lt (K := ℝ)).2 manuscript_case2X11_endpoint_lt_printed)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2X11SubstituteRat : ℚ :=
  barrierCase2XApproxRat Case2PointData.X11 (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) +
    (barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491)) +
    (barrierWeightedComplexLogRat (-33138961 / 50000000) (-(31907569 / 100000000)) (-2) (-(-1)) (72161285330618364409 / 39062500000000000000) (-(44745509 / 705254491))) +
    (barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557)) +
    (barrierWeightedComplexLogRat (-1231651 / 100000000) (-(-1200529 / 20000000)) (-2) (-(-1)) (234036474322422598249 / 156250000000000000000) (-(-6697292557 / 20572292557))) +
    (barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830)) +
    (barrierWeightedComplexLogRat (-1612959 / 50000000) (-(-4464117 / 50000000)) (-3) (-(-2)) (18347561655277840040989 / 12207031250000000000000) (-(32197927717 / 131570722830))) +
    (barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830)) +
    (barrierWeightedComplexLogRat (-32899 / 1562500) (-(9091287 / 100000000)) (-1) (-(-2)) (61118574509195980040989 / 48828125000000000000000) (-(69092072283 / 237370722830))) +
    (barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1)) +
    (barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000)) +
    (barrierWeightedComplexLogRat (13619357 / 100000000) (-(600749 / 3125000)) (0) (-(0)) (16603427027813684331961 / 15625000000000000000000) (-(-31279818219 / 125000000000))) +
    (barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000)) +
    (barrierWeightedComplexLogRat (-7835271 / 50000000) (-(15094393 / 100000000)) (0) (-(0)) (677105581362858928921 / 625000000000000000000) (-(-7218419589 / 25000000000))) +
    (barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000)) +
    (barrierWeightedComplexLogRat (-3346771 / 100000000) (-(-5956127 / 100000000)) (0) (-(0)) (273467453255536501061321 / 250000000000000000000000) (-(-153190904611 / 500000000000))) +
    (barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000)) +
    (barrierWeightedComplexLogRat (2055213 / 200000000) (-(21715849 / 200000000)) (0) (-(0)) (107388414696773984390689 / 97656250000000000000000) (-(-98651734383 / 312500000000)))

theorem manuscript_case2X11_substitute_interval :
    manuscriptCase2X11SubstituteRat ∈ Set.Icc manuscriptCase2X11Interval.1 manuscriptCase2X11Interval.2 := by
  have hf := manuscript_x_substitute_interval (65 / 48) (barrierCase2XRat Case2PointData.X11) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase2XApproxRat Case2PointData.X11 (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000)) ∈ Set.Icc manuscriptCase2X11FieldInterval.1 manuscriptCase2X11FieldInterval.2 at hf
  have ht0 := manuscript_weightedComplexLogRat_interval (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XP0Interval.1 manuscriptCase2X11XP0Interval.2 at ht0
  have ht1 := manuscript_weightedComplexLogRat_interval (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XP1Interval.1 manuscriptCase2X11XP1Interval.2 at ht1
  have ht2 := manuscript_weightedComplexLogRat_interval (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491) (by norm_num)
  change (barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491)) ∈ Set.Icc manuscriptCase2X11XP2Interval.1 manuscriptCase2X11XP2Interval.2 at ht2
  have hc2 := manuscript_weightedComplexLogRat_conj (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491)
  have ht3 := manuscript_weightedComplexLogRat_interval (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557) (by norm_num)
  change (barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557)) ∈ Set.Icc manuscriptCase2X11XP4Interval.1 manuscriptCase2X11XP4Interval.2 at ht3
  have hc3 := manuscript_weightedComplexLogRat_conj (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557)
  have ht4 := manuscript_weightedComplexLogRat_interval (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830) (by norm_num)
  change (barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830)) ∈ Set.Icc manuscriptCase2X11XP6Interval.1 manuscriptCase2X11XP6Interval.2 at ht4
  have hc4 := manuscript_weightedComplexLogRat_conj (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830)
  have ht5 := manuscript_weightedComplexLogRat_interval (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830) (by norm_num)
  change (barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830)) ∈ Set.Icc manuscriptCase2X11XP8Interval.1 manuscriptCase2X11XP8Interval.2 at ht5
  have hc5 := manuscript_weightedComplexLogRat_conj (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830)
  have ht6 := manuscript_weightedComplexLogRat_interval (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XV0Interval.1 manuscriptCase2X11XV0Interval.2 at ht6
  have ht7 := manuscript_weightedComplexLogRat_interval (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XV1Interval.1 manuscriptCase2X11XV1Interval.2 at ht7
  have ht8 := manuscript_weightedComplexLogRat_interval (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XV2Interval.1 manuscriptCase2X11XV2Interval.2 at ht8
  have ht9 := manuscript_weightedComplexLogRat_interval (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XV3Interval.1 manuscriptCase2X11XV3Interval.2 at ht9
  have ht10 := manuscript_weightedComplexLogRat_interval (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1) (by norm_num)
  change (barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1)) ∈ Set.Icc manuscriptCase2X11XV4Interval.1 manuscriptCase2X11XV4Interval.2 at ht10
  have ht11 := manuscript_weightedComplexLogRat_interval (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000) (by norm_num)
  change (barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000)) ∈ Set.Icc manuscriptCase2X11XV5Interval.1 manuscriptCase2X11XV5Interval.2 at ht11
  have hc11 := manuscript_weightedComplexLogRat_conj (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000)
  have ht12 := manuscript_weightedComplexLogRat_interval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000) (by norm_num)
  change (barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000)) ∈ Set.Icc manuscriptCase2X11XV7Interval.1 manuscriptCase2X11XV7Interval.2 at ht12
  have hc12 := manuscript_weightedComplexLogRat_conj (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000)
  have ht13 := manuscript_weightedComplexLogRat_interval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000) (by norm_num)
  change (barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000)) ∈ Set.Icc manuscriptCase2X11XV9Interval.1 manuscriptCase2X11XV9Interval.2 at ht13
  have hc13 := manuscript_weightedComplexLogRat_conj (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000)
  have ht14 := manuscript_weightedComplexLogRat_interval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000) (by norm_num)
  change (barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000)) ∈ Set.Icc manuscriptCase2X11XV11Interval.1 manuscriptCase2X11XV11Interval.2 at ht14
  have hc14 := manuscript_weightedComplexLogRat_conj (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000)
  constructor
  · change manuscriptCase2X11Interval.1 ≤ manuscriptCase2X11SubstituteRat
    dsimp only [manuscriptCase2X11Interval, manuscriptCase2X11SubstituteRat]
    linarith only [hf.1, ht0.1, ht1.1, ht2.1, ht3.1, ht4.1, ht5.1, ht6.1, ht7.1, ht8.1, ht9.1, ht10.1, ht11.1, ht12.1, ht13.1, ht14.1, hc2, hc3, hc4, hc5, hc11, hc12, hc13, hc14]
  · change manuscriptCase2X11SubstituteRat ≤ manuscriptCase2X11Interval.2
    dsimp only [manuscriptCase2X11Interval, manuscriptCase2X11SubstituteRat]
    linarith only [hf.2, ht0.2, ht1.2, ht2.2, ht3.2, ht4.2, ht5.2, ht6.2, ht7.2, ht8.2, ht9.2, ht10.2, ht11.2, ht12.2, ht13.2, ht14.2, hc2, hc3, hc4, hc5, hc11, hc12, hc13, hc14]

theorem manuscript_case2X11_substitute_cutoff :
    manuscriptCase2X11SubstituteRat < ((-123 / 125) : ℚ) := by
  have hp : manuscriptCase2X11PrintedUpper < ((-123 / 125) : ℚ) := by norm_num [manuscriptCase2X11PrintedUpper]
  exact manuscript_case2X11_substitute_interval.2.trans_lt (manuscript_case2X11_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2X11RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (65 / 48) (barrierCase2XRat Case2PointData.X11) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) +
    (manuscriptRoundedWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491)) +
    (manuscriptRoundedWeightedComplexLogRat (-33138961 / 50000000) (-(31907569 / 100000000)) (-2) (-(-1)) (72161285330618364409 / 39062500000000000000) (-(44745509 / 705254491))) +
    (manuscriptRoundedWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557)) +
    (manuscriptRoundedWeightedComplexLogRat (-1231651 / 100000000) (-(-1200529 / 20000000)) (-2) (-(-1)) (234036474322422598249 / 156250000000000000000) (-(-6697292557 / 20572292557))) +
    (manuscriptRoundedWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830)) +
    (manuscriptRoundedWeightedComplexLogRat (-1612959 / 50000000) (-(-4464117 / 50000000)) (-3) (-(-2)) (18347561655277840040989 / 12207031250000000000000) (-(32197927717 / 131570722830))) +
    (manuscriptRoundedWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830)) +
    (manuscriptRoundedWeightedComplexLogRat (-32899 / 1562500) (-(9091287 / 100000000)) (-1) (-(-2)) (61118574509195980040989 / 48828125000000000000000) (-(69092072283 / 237370722830))) +
    (manuscriptRoundedWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000)) +
    (manuscriptRoundedWeightedComplexLogRat (13619357 / 100000000) (-(600749 / 3125000)) (0) (-(0)) (16603427027813684331961 / 15625000000000000000000) (-(-31279818219 / 125000000000))) +
    (manuscriptRoundedWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000)) +
    (manuscriptRoundedWeightedComplexLogRat (-7835271 / 50000000) (-(15094393 / 100000000)) (0) (-(0)) (677105581362858928921 / 625000000000000000000) (-(-7218419589 / 25000000000))) +
    (manuscriptRoundedWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000)) +
    (manuscriptRoundedWeightedComplexLogRat (-3346771 / 100000000) (-(-5956127 / 100000000)) (0) (-(0)) (273467453255536501061321 / 250000000000000000000000) (-(-153190904611 / 500000000000))) +
    (manuscriptRoundedWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000)) +
    (manuscriptRoundedWeightedComplexLogRat (2055213 / 200000000) (-(21715849 / 200000000)) (0) (-(0)) (107388414696773984390689 / 97656250000000000000000) (-(-98651734383 / 312500000000)))

theorem manuscript_case2X11_additional_rounding_error :
    |(manuscriptCase2X11SubstituteRat : ℝ) - (manuscriptCase2X11RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase2XApproxRat Case2PointData.X11 (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (65 / 48) (barrierCase2XRat Case2PointData.X11) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((65 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a1 : ℚ := (barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1))
  let r1 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1))
  let e1 : ℝ := (|(((-2334613 / 12500000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a2 : ℚ := (barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1))
  let r2 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1))
  let e2 : ℝ := (|(((-2141509 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a3 : ℚ := (barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491))
  let r3 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491))
  let e3 : ℝ := (|(((-33138961 / 50000000) : ℚ) : ℝ)| + |(((31907569 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a4 : ℚ := (barrierWeightedComplexLogRat (-33138961 / 50000000) (-(31907569 / 100000000)) (-2) (-(-1)) (72161285330618364409 / 39062500000000000000) (-(44745509 / 705254491)))
  let r4 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-33138961 / 50000000) (-(31907569 / 100000000)) (-2) (-(-1)) (72161285330618364409 / 39062500000000000000) (-(44745509 / 705254491)))
  let e4 : ℝ := (|(((-33138961 / 50000000) : ℚ) : ℝ)| + |(((-(31907569 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a5 : ℚ := (barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557))
  let r5 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557))
  let e5 : ℝ := (|(((-1231651 / 100000000) : ℚ) : ℝ)| + |(((-1200529 / 20000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a6 : ℚ := (barrierWeightedComplexLogRat (-1231651 / 100000000) (-(-1200529 / 20000000)) (-2) (-(-1)) (234036474322422598249 / 156250000000000000000) (-(-6697292557 / 20572292557)))
  let r6 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1231651 / 100000000) (-(-1200529 / 20000000)) (-2) (-(-1)) (234036474322422598249 / 156250000000000000000) (-(-6697292557 / 20572292557)))
  let e6 : ℝ := (|(((-1231651 / 100000000) : ℚ) : ℝ)| + |(((-(-1200529 / 20000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a7 : ℚ := (barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830))
  let r7 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830))
  let e7 : ℝ := (|(((-1612959 / 50000000) : ℚ) : ℝ)| + |(((-4464117 / 50000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a8 : ℚ := (barrierWeightedComplexLogRat (-1612959 / 50000000) (-(-4464117 / 50000000)) (-3) (-(-2)) (18347561655277840040989 / 12207031250000000000000) (-(32197927717 / 131570722830)))
  let r8 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1612959 / 50000000) (-(-4464117 / 50000000)) (-3) (-(-2)) (18347561655277840040989 / 12207031250000000000000) (-(32197927717 / 131570722830)))
  let e8 : ℝ := (|(((-1612959 / 50000000) : ℚ) : ℝ)| + |(((-(-4464117 / 50000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a9 : ℚ := (barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830))
  let r9 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830))
  let e9 : ℝ := (|(((-32899 / 1562500) : ℚ) : ℝ)| + |(((9091287 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a10 : ℚ := (barrierWeightedComplexLogRat (-32899 / 1562500) (-(9091287 / 100000000)) (-1) (-(-2)) (61118574509195980040989 / 48828125000000000000000) (-(69092072283 / 237370722830)))
  let r10 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-32899 / 1562500) (-(9091287 / 100000000)) (-1) (-(-2)) (61118574509195980040989 / 48828125000000000000000) (-(69092072283 / 237370722830)))
  let e10 : ℝ := (|(((-32899 / 1562500) : ℚ) : ℝ)| + |(((-(9091287 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a11 : ℚ := (barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1))
  let r11 : ℚ := (manuscriptRoundedWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1))
  let e11 : ℝ := (|(((15199211 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a12 : ℚ := (barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1))
  let r12 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1))
  let e12 : ℝ := (|(((2225831 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a13 : ℚ := (barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1))
  let r13 : ℚ := (manuscriptRoundedWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1))
  let e13 : ℝ := (|(((1272699 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a14 : ℚ := (barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1))
  let r14 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1))
  let e14 : ℝ := (|(((-2466317 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a15 : ℚ := (barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1))
  let r15 : ℚ := (manuscriptRoundedWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1))
  let e15 : ℝ := (|(((11618157 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a16 : ℚ := (barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000))
  let r16 : ℚ := (manuscriptRoundedWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000))
  let e16 : ℝ := (|(((13619357 / 100000000) : ℚ) : ℝ)| + |(((600749 / 3125000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a17 : ℚ := (barrierWeightedComplexLogRat (13619357 / 100000000) (-(600749 / 3125000)) (0) (-(0)) (16603427027813684331961 / 15625000000000000000000) (-(-31279818219 / 125000000000)))
  let r17 : ℚ := (manuscriptRoundedWeightedComplexLogRat (13619357 / 100000000) (-(600749 / 3125000)) (0) (-(0)) (16603427027813684331961 / 15625000000000000000000) (-(-31279818219 / 125000000000)))
  let e17 : ℝ := (|(((13619357 / 100000000) : ℚ) : ℝ)| + |(((-(600749 / 3125000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a18 : ℚ := (barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000))
  let r18 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000))
  let e18 : ℝ := (|(((-7835271 / 50000000) : ℚ) : ℝ)| + |(((15094393 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a19 : ℚ := (barrierWeightedComplexLogRat (-7835271 / 50000000) (-(15094393 / 100000000)) (0) (-(0)) (677105581362858928921 / 625000000000000000000) (-(-7218419589 / 25000000000)))
  let r19 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-7835271 / 50000000) (-(15094393 / 100000000)) (0) (-(0)) (677105581362858928921 / 625000000000000000000) (-(-7218419589 / 25000000000)))
  let e19 : ℝ := (|(((-7835271 / 50000000) : ℚ) : ℝ)| + |(((-(15094393 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a20 : ℚ := (barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000))
  let r20 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000))
  let e20 : ℝ := (|(((-3346771 / 100000000) : ℚ) : ℝ)| + |(((-5956127 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a21 : ℚ := (barrierWeightedComplexLogRat (-3346771 / 100000000) (-(-5956127 / 100000000)) (0) (-(0)) (273467453255536501061321 / 250000000000000000000000) (-(-153190904611 / 500000000000)))
  let r21 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-3346771 / 100000000) (-(-5956127 / 100000000)) (0) (-(0)) (273467453255536501061321 / 250000000000000000000000) (-(-153190904611 / 500000000000)))
  let e21 : ℝ := (|(((-3346771 / 100000000) : ℚ) : ℝ)| + |(((-(-5956127 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a22 : ℚ := (barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000))
  let r22 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000))
  let e22 : ℝ := (|(((2055213 / 200000000) : ℚ) : ℝ)| + |(((21715849 / 200000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a23 : ℚ := (barrierWeightedComplexLogRat (2055213 / 200000000) (-(21715849 / 200000000)) (0) (-(0)) (107388414696773984390689 / 97656250000000000000000) (-(-98651734383 / 312500000000)))
  let r23 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2055213 / 200000000) (-(21715849 / 200000000)) (0) (-(0)) (107388414696773984390689 / 97656250000000000000000) (-(-98651734383 / 312500000000)))
  let e23 : ℝ := (|(((2055213 / 200000000) : ℚ) : ℝ)| + |(((-(21715849 / 200000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (65 / 48) (barrierCase2XRat Case2PointData.X11) (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have h1 : |(a1 : ℝ) - (r1 : ℝ)| ≤ e1 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h2 : |(a2 : ℝ) - (r2 : ℝ)| ≤ e2 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h3 : |(a3 : ℝ) - (r3 : ℝ)| ≤ e3 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491) (by norm_num) (by norm_num)
  have h4 : |(a4 : ℝ) - (r4 : ℝ)| ≤ e4 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-33138961 / 50000000) (-(31907569 / 100000000)) (-2) (-(-1)) (72161285330618364409 / 39062500000000000000) (-(44745509 / 705254491)) (by norm_num) (by norm_num)
  have h5 : |(a5 : ℝ) - (r5 : ℝ)| ≤ e5 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557) (by norm_num) (by norm_num)
  have h6 : |(a6 : ℝ) - (r6 : ℝ)| ≤ e6 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1231651 / 100000000) (-(-1200529 / 20000000)) (-2) (-(-1)) (234036474322422598249 / 156250000000000000000) (-(-6697292557 / 20572292557)) (by norm_num) (by norm_num)
  have h7 : |(a7 : ℝ) - (r7 : ℝ)| ≤ e7 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830) (by norm_num) (by norm_num)
  have h8 : |(a8 : ℝ) - (r8 : ℝ)| ≤ e8 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1612959 / 50000000) (-(-4464117 / 50000000)) (-3) (-(-2)) (18347561655277840040989 / 12207031250000000000000) (-(32197927717 / 131570722830)) (by norm_num) (by norm_num)
  have h9 : |(a9 : ℝ) - (r9 : ℝ)| ≤ e9 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830) (by norm_num) (by norm_num)
  have h10 : |(a10 : ℝ) - (r10 : ℝ)| ≤ e10 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-32899 / 1562500) (-(9091287 / 100000000)) (-1) (-(-2)) (61118574509195980040989 / 48828125000000000000000) (-(69092072283 / 237370722830)) (by norm_num) (by norm_num)
  have h11 : |(a11 : ℝ) - (r11 : ℝ)| ≤ e11 := by
    exact manuscript_rounded_weighted_complex_log_error_le (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h12 : |(a12 : ℝ) - (r12 : ℝ)| ≤ e12 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1) (by norm_num) (by norm_num)
  have h13 : |(a13 : ℝ) - (r13 : ℝ)| ≤ e13 := by
    exact manuscript_rounded_weighted_complex_log_error_le (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h14 : |(a14 : ℝ) - (r14 : ℝ)| ≤ e14 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h15 : |(a15 : ℝ) - (r15 : ℝ)| ≤ e15 := by
    exact manuscript_rounded_weighted_complex_log_error_le (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h16 : |(a16 : ℝ) - (r16 : ℝ)| ≤ e16 := by
    exact manuscript_rounded_weighted_complex_log_error_le (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000) (by norm_num) (by norm_num)
  have h17 : |(a17 : ℝ) - (r17 : ℝ)| ≤ e17 := by
    exact manuscript_rounded_weighted_complex_log_error_le (13619357 / 100000000) (-(600749 / 3125000)) (0) (-(0)) (16603427027813684331961 / 15625000000000000000000) (-(-31279818219 / 125000000000)) (by norm_num) (by norm_num)
  have h18 : |(a18 : ℝ) - (r18 : ℝ)| ≤ e18 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000) (by norm_num) (by norm_num)
  have h19 : |(a19 : ℝ) - (r19 : ℝ)| ≤ e19 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-7835271 / 50000000) (-(15094393 / 100000000)) (0) (-(0)) (677105581362858928921 / 625000000000000000000) (-(-7218419589 / 25000000000)) (by norm_num) (by norm_num)
  have h20 : |(a20 : ℝ) - (r20 : ℝ)| ≤ e20 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000) (by norm_num) (by norm_num)
  have h21 : |(a21 : ℝ) - (r21 : ℝ)| ≤ e21 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-3346771 / 100000000) (-(-5956127 / 100000000)) (0) (-(0)) (273467453255536501061321 / 250000000000000000000000) (-(-153190904611 / 500000000000)) (by norm_num) (by norm_num)
  have h22 : |(a22 : ℝ) - (r22 : ℝ)| ≤ e22 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000) (by norm_num) (by norm_num)
  have h23 : |(a23 : ℝ) - (r23 : ℝ)| ≤ e23 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2055213 / 200000000) (-(21715849 / 200000000)) (0) (-(0)) (107388414696773984390689 / 97656250000000000000000) (-(-98651734383 / 312500000000)) (by norm_num) (by norm_num)
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
  have hs14 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) a14 r14 hs13 h14
  have hs15 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14) a15 r15 hs14 h15
  have hs16 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15) a16 r16 hs15 h16
  have hs17 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16) a17 r17 hs16 h17
  have hs18 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17) a18 r18 hs17 h18
  have hs19 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18) a19 r19 hs18 h19
  have hs20 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19) a20 r20 hs19 h20
  have hs21 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19 + a20) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20) a21 r21 hs20 h21
  have hs22 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19 + a20 + a21) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20 + r21) a22 r22 hs21 h22
  have hs23 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19 + a20 + a21 + a22) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20 + r21 + r22) a23 r23 hs22 h23
  have hbudget : e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 + e14 + e15 + e16 + e17 + e18 + e19 + e20 + e21 + e22 + e23 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, manuscriptTermRoundStep]
  change |(manuscriptCase2X11SubstituteRat : ℝ) - (manuscriptCase2X11RoundedSubstituteRat : ℝ)| ≤ e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 + e14 + e15 + e16 + e17 + e18 + e19 + e20 + e21 + e22 + e23 at hs23
  exact hs23.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case2X11_actual_substitution_error :
    |barrierCase2X (Case2PointData.X11 : ℝ) - (manuscriptCase2X11SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase2X11Interval.2 - manuscriptCase2X11Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case2X11_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase2X11Interval.1 manuscriptCase2X11Interval.2 manuscriptCase2X11SubstituteRat
    (barrierCase2X (Case2PointData.X11 : ℝ)) (35 / 1000000000000000)
    manuscript_case2X11_interval manuscript_case2X11_substitute_interval hw

end InternalCatalan

end

end

end OAI

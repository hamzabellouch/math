import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y8YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357)

private theorem manuscriptCase2Y8YV7_arg_eq : barrierCase2Y8YV7LogArg = barrierComplex (19 / 100) (-61217364357 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV7LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV7Interval.1 : ℝ) (manuscriptCase2Y8YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y8YV7LogArg).re ∈ _
  rw [manuscriptCase2Y8YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y8YV7LogArg (0) (-2) (3837815698817694023449 / 2500000000000000000000) (61217364357 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (61217364357 / 25000000000) : ℚ) = (9500000000 / 61217364357) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV7_rounded_endpoints :
    (-1802803809477563045941335720355716492973 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV7Interval.1 ∧ manuscriptCase2Y8YV7Interval.2 ≤ (-901401904738781468250201928910366259329 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1802803809477563045941335720355716492973 / 10000000000000000000000000000000000000000) : ℝ) ((-901401904738781468250201928910366259329 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1802803809477563045941335720355716492973 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV7Interval.2 : ℝ) ≤ ((-901401904738781468250201928910366259329 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV7_exact_interval.1, manuscriptCase2Y8YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081)

private theorem manuscriptCase2Y8YV9_arg_eq : barrierCase2Y8YV9LogArg = barrierComplex (3519 / 40000) (-1299168510243 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV9LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV9Interval.1 : ℝ) (manuscriptCase2Y8YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y8YV9LogArg).re ∈ _
  rw [manuscriptCase2Y8YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y8YV9LogArg (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (1299168510243 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1299168510243 / 500000000000) : ℚ) = (29325000000 / 433056170081) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV9_rounded_endpoints :
    (196734747812496772706604677212437785211 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV9Interval.1 ∧ manuscriptCase2Y8YV9Interval.2 ≤ (24591843476562097667938580913891970889 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((196734747812496772706604677212437785211 / 2000000000000000000000000000000000000000) : ℝ) ((24591843476562097667938580913891970889 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((196734747812496772706604677212437785211 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV9Interval.2 : ℝ) ≤ ((24591843476562097667938580913891970889 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV9_exact_interval.1, manuscriptCase2Y8YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y8YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879)

private theorem manuscriptCase2Y8YV11_arg_eq : barrierCase2Y8YV11LogArg = barrierComplex (496 / 15625) (-836637312879 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y8YV11LogArg, Case2PointData.Y8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y8YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y8YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y8YV11Interval.1 : ℝ) (manuscriptCase2Y8YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y8YV11LogArg).re ∈ _
  rw [manuscriptCase2Y8YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y8YV11LogArg (0) (-2) (700355618901393739268641 / 390625000000000000000000) (836637312879 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (836637312879 / 312500000000) : ℚ) = (19840000000 / 836637312879) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y8YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y8YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y8YV11_rounded_endpoints :
    (-1709813057147518084071180773546975929679 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y8YV11Interval.1 ∧ manuscriptCase2Y8YV11Interval.2 ≤ (-341962611429503601069295075152616971233 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y8YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y8YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1709813057147518084071180773546975929679 / 10000000000000000000000000000000000000000) : ℝ) ((-341962611429503601069295075152616971233 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1709813057147518084071180773546975929679 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y8YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y8YV11Interval.2 : ℝ) ≤ ((-341962611429503601069295075152616971233 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y8YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y8YV11_exact_interval.1, manuscriptCase2Y8YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI

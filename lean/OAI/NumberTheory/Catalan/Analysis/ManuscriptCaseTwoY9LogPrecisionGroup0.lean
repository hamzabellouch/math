import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y9YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (334231098797379233641 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y9YV0_arg_eq : barrierCase2Y9YV0LogArg = barrierComplex (18281988371 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV0LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV0Interval.1 : ℝ) (manuscriptCase2Y9YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y9YV0LogArg).re ∈ _
  rw [manuscriptCase2Y9YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y9YV0LogArg (3) (0) (334231098797379233641 / 312500000000000000000) (18281988371 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (18281988371 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV0_rounded_endpoints :
    (-32627686307122423786284954253202858317 / 200000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV0Interval.1 ∧ manuscriptCase2Y9YV0Interval.2 ≤ (-815692157678060594503174925582865418521 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-32627686307122423786284954253202858317 / 200000000000000000000000000000000000000) : ℝ) ((-815692157678060594503174925582865418521 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-32627686307122423786284954253202858317 / 200000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV0Interval.2 : ℝ) ≤ ((-815692157678060594503174925582865418521 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV0_exact_interval.1, manuscriptCase2Y9YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (2929078864762563102769 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y9YV1_arg_eq : barrierCase2Y9YV1LogArg = barrierComplex (54120965113 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV1LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV1Interval.1 : ℝ) (manuscriptCase2Y9YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y9YV1LogArg).re ∈ _
  rw [manuscriptCase2Y9YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y9YV1LogArg (3) (0) (2929078864762563102769 / 1953125000000000000000) (54120965113 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (54120965113 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV1_rounded_endpoints :
    (-553051979435211727465133784229326387019 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV1Interval.1 ∧ manuscriptCase2Y9YV1Interval.2 ≤ (-55305197943521172737495428659184896451 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-553051979435211727465133784229326387019 / 10000000000000000000000000000000000000000) : ℝ) ((-55305197943521172737495428659184896451 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-553051979435211727465133784229326387019 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV1Interval.2 : ℝ) ≤ ((-55305197943521172737495428659184896451 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV1_exact_interval.1, manuscriptCase2Y9YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-3) (0) (508418072651587270561 / 488281250000000000000) (0 / 1)

private theorem manuscriptCase2Y9YV2_arg_eq : barrierCase2Y9YV2LogArg = barrierComplex (22548127919 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV2LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV2Interval.1 : ℝ) (manuscriptCase2Y9YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y9YV2LogArg).re ∈ _
  rw [manuscriptCase2Y9YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y9YV2LogArg (-3) (0) (508418072651587270561 / 488281250000000000000) (22548127919 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (22548127919 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV2_rounded_endpoints :
    (64876755081494256866727857304440090023 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV2Interval.1 ∧ manuscriptCase2Y9YV2Interval.2 ≤ (259507020325977027518474803188432490151 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((64876755081494256866727857304440090023 / 2500000000000000000000000000000000000000) : ℝ) ((259507020325977027518474803188432490151 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((64876755081494256866727857304440090023 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV2Interval.2 : ℝ) ≤ ((259507020325977027518474803188432490151 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV2_exact_interval.1, manuscriptCase2Y9YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI

import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX15

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X15XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-5) (0) (411780064346696231761 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2X15XV3_arg_eq : barrierCase2X15XV3LogArg = barrierComplex (20292364681 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV3LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV3Interval.1 : ℝ) (manuscriptCase2X15XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X15XV3LogArg).re ∈ _
  rw [manuscriptCase2X15XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X15XV3LogArg (-5) (0) (411780064346696231761 / 312500000000000000000) (20292364681 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (20292364681 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV3_rounded_endpoints :
    (786718372302568637118659948474403676017 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV3Interval.1 ∧ manuscriptCase2X15XV3Interval.2 ≤ (393359186151284318642598959939520491087 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((786718372302568637118659948474403676017 / 10000000000000000000000000000000000000000) : ℝ) ((393359186151284318642598959939520491087 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((786718372302568637118659948474403676017 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV3Interval.2 : ℝ) ≤ ((393359186151284318642598959939520491087 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV3_exact_interval.1, manuscriptCase2X15XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-6) (0) (11880550875630518809729 / 6103515625000000000000) (0 / 1)

private theorem manuscriptCase2X15XV4_arg_eq : barrierCase2X15XV4LogArg = barrierComplex (108997939777 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV4LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV4Interval.1 : ℝ) (manuscriptCase2X15XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XV4LogArg).re ∈ _
  rw [manuscriptCase2X15XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X15XV4LogArg (-6) (0) (11880550875630518809729 / 6103515625000000000000) (108997939777 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (108997939777 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV4_rounded_endpoints :
    (-2029021275464385196150146091045157012187 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV4Interval.1 ∧ manuscriptCase2X15XV4Interval.2 ≤ (-507255318866096298914911420955624936123 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-2029021275464385196150146091045157012187 / 10000000000000000000000000000000000000000) : ℝ) ((-507255318866096298914911420955624936123 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2029021275464385196150146091045157012187 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV4Interval.2 : ℝ) ≤ ((-507255318866096298914911420955624936123 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV4_exact_interval.1, manuscriptCase2X15XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (89268366044075138416921 / 62500000000000000000000) (86389590661 / 413610409339)

private theorem manuscriptCase2X15XV5_arg_eq : barrierCase2X15XV5LogArg = barrierComplex (1 / 1) (-163610409339 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV5LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV5Interval.1 : ℝ) (manuscriptCase2X15XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X15XV5LogArg).re ∈ _
  rw [manuscriptCase2X15XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X15XV5LogArg (0) (-1) (89268366044075138416921 / 62500000000000000000000) (413610409339 / 250000000000) (86389590661 / 250000000000)
  have hratio : ((86389590661 / 250000000000) / (413610409339 / 250000000000) : ℚ) = (86389590661 / 413610409339) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV5_rounded_endpoints :
    (678382035171106083114612514830768576391 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV5Interval.1 ∧ manuscriptCase2X15XV5Interval.2 ≤ (1356764070342212235920300779760309448379 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((678382035171106083114612514830768576391 / 5000000000000000000000000000000000000000) : ℝ) ((1356764070342212235920300779760309448379 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((678382035171106083114612514830768576391 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV5Interval.2 : ℝ) ≤ ((1356764070342212235920300779760309448379 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV5_exact_interval.1, manuscriptCase2X15XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI

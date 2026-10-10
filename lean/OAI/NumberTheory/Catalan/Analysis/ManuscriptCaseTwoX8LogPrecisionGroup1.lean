import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX8Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X8XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (23446017036877972041 / 19531250000000000000) (-30106607 / 2282393393)

private theorem manuscriptCase2X8XP4_arg_eq : barrierCase2X8XP4LogArg = barrierComplex (111 / 400) (3378430179 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP4LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP4Interval.1 : ℝ) (manuscriptCase2X8XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XP4LogArg).re ∈ _
  rw [manuscriptCase2X8XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X8XP4LogArg (-3) (1) (23446017036877972041 / 19531250000000000000) (6847180179 / 12500000000) (-90319821 / 12500000000)
  have hratio : ((-90319821 / 12500000000) / (6847180179 / 12500000000) : ℚ) = (-30106607 / 2282393393) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP4_rounded_endpoints :
    (580336234544124081496267176931579773319 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP4Interval.1 ∧ manuscriptCase2X8XP4Interval.2 ≤ (580336234544124103282114324937595059367 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((580336234544124081496267176931579773319 / 10000000000000000000000000000000000000000) : ℝ) ((580336234544124103282114324937595059367 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((580336234544124081496267176931579773319 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP4Interval.2 : ℝ) ≤ ((580336234544124103282114324937595059367 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP4_exact_interval.1, manuscriptCase2X8XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-3) (1) (6100412351399358384701 / 3051757812500000000000) (42264855709 / 102051490311)

private theorem manuscriptCase2X8XP6_arg_eq : barrierCase2X8XP6LogArg = barrierComplex (29893317301 / 156250000000) (7215817301 / 15625000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP6LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP6Interval.1 : ℝ) (manuscriptCase2X8XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X8XP6LogArg).re ∈ _
  rw [manuscriptCase2X8XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X8XP6LogArg (-3) (1) (6100412351399358384701 / 3051757812500000000000) (102051490311 / 156250000000) (42264855709 / 156250000000)
  have hratio : ((42264855709 / 156250000000) / (102051490311 / 156250000000) : ℚ) = (42264855709 / 102051490311) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP6_rounded_endpoints :
    (1275471699567313854818996539649068679867 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP6Interval.1 ∧ manuscriptCase2X8XP6Interval.2 ≤ (318867924891828471818888149279459423363 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((1275471699567313854818996539649068679867 / 10000000000000000000000000000000000000000) : ℝ) ((318867924891828471818888149279459423363 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1275471699567313854818996539649068679867 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP6Interval.2 : ℝ) ≤ ((318867924891828471818888149279459423363 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP6_exact_interval.1, manuscriptCase2X8XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (801509562523068384701 / 762939453125000000000) (-1493509689 / 40009855709)

private theorem manuscriptCase2X8XP8_arg_eq : barrierCase2X8XP8LogArg = barrierComplex (20751682699 / 156250000000) (1925817301 / 15625000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XP8LogArg, Case2PointData.X8, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XP8Interval.1 : ℝ) (manuscriptCase2X8XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X8XP8LogArg).re ∈ _
  rw [manuscriptCase2X8XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X8XP8LogArg (-5) (1) (801509562523068384701 / 762939453125000000000) (40009855709 / 156250000000) (-1493509689 / 156250000000)
  have hratio : ((-1493509689 / 156250000000) / (40009855709 / 156250000000) : ℚ) = (-1493509689 / 40009855709) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XP8_rounded_endpoints :
    (-64087557819849074205821813873106848673 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X8XP8Interval.1 ∧ manuscriptCase2X8XP8Interval.2 ≤ (-160218894549622669000061616492856191563 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-64087557819849074205821813873106848673 / 2000000000000000000000000000000000000000) : ℝ) ((-160218894549622669000061616492856191563 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-64087557819849074205821813873106848673 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XP8Interval.2 : ℝ) ≤ ((-160218894549622669000061616492856191563 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XP8_exact_interval.1, manuscriptCase2X8XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI

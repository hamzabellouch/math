import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogReality
import OAI.NumberTheory.Catalan.Polynomial.ManuscriptRationalIntervals

namespace OAI

noncomputable section

namespace InternalCatalan

section
open Filter
open scoped BigOperators Topology

private theorem manuscriptAtanJ_neg (t : ℝ) : barrierAtanJ (-t) = -barrierAtanJ t := by
  unfold barrierAtanJ
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(odd_two_mul_add_one j).neg_pow t]
  ring

theorem manuscript_atanJ_nonneg_interval (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.arctan t ∈ Set.Icc (barrierAtanJ t) (barrierAtanJ t + t ^ 49 / 49) := by
  let f : ℕ → ℝ := fun j => t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)
  have ht1 : t ≤ 1 := by linarith
  have hf : Antitone f := by
    intro i j hij
    dsimp only [f]
    exact div_le_div₀ (pow_nonneg ht0 _)
      (pow_le_pow_of_le_one ht0 ht1 (by omega)) (by positivity)
      (by exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega))
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  have hconv : Tendsto
      (fun n => ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * f j)
      atTop (𝓝 (Real.arctan t)) := by
    simpa only [f, mul_div_assoc] using (Real.hasSum_arctan hnorm).tendsto_sum_nat
  have hpartial : (∑ j ∈ Finset.range 24, (-1 : ℝ) ^ j * f j) =
      barrierAtanJ t := by simp only [barrierAtanJ, f, mul_div_assoc]
  have hlast : (-1 : ℝ) ^ 24 * f 24 = t ^ 49 / 49 := by norm_num [f]
  constructor
  · have h := Antitone.alternating_series_le_tendsto hconv hf 12
    change (∑ j ∈ Finset.range 24, (-1 : ℝ) ^ j * f j) ≤ Real.arctan t at h
    rwa [hpartial] at h
  · have h := Antitone.tendsto_le_alternating_series hconv hf 12
    change Real.arctan t ≤ ∑ j ∈ Finset.range (24 + 1), (-1 : ℝ) ^ j * f j at h
    rwa [Finset.sum_range_succ, hpartial, hlast] at h

theorem manuscript_atanJ_neg_interval (t : ℝ)
    (ht0 : t < 0) (ht : |t| ≤ 1 / 2) :
    Real.arctan t ∈ Set.Icc (barrierAtanJ t - |t| ^ 49 / 49) (barrierAtanJ t) := by
  have hnt : -t ≤ 1 / 2 := by simpa only [abs_of_neg ht0] using ht
  have h := manuscript_atanJ_nonneg_interval (-t) (by linarith) hnt
  rw [Real.arctan_neg, manuscriptAtanJ_neg] at h
  rw [abs_of_neg ht0]
  constructor <;> linarith [h.1, h.2]

def manuscriptAtanInterval (t : ℚ) : ℚ × ℚ :=
  if 0 ≤ t then (barrierAtanJRat t, barrierAtanJRat t + |t| ^ 49 / 49)
  else (barrierAtanJRat t - |t| ^ 49 / 49, barrierAtanJRat t)

def manuscriptPiQuarterInterval : ℚ × ℚ :=
  manuscriptIntervalAdd (manuscriptAtanInterval (1 / 2)) (manuscriptAtanInterval (1 / 3))

def manuscriptArgInterval (k : ℤ) (t : ℚ) : ℚ × ℚ :=
  manuscriptIntervalAdd (manuscriptIntervalScale (k : ℚ) manuscriptPiQuarterInterval)
    (manuscriptAtanInterval t)

theorem manuscript_atan_interval (t : ℚ) (ht : |(t : ℝ)| ≤ 1 / 2) :
    Real.arctan (t : ℝ) ∈ Set.Icc ((manuscriptAtanInterval t).1 : ℝ)
      ((manuscriptAtanInterval t).2 : ℝ) := by
  by_cases hq : 0 ≤ t
  · have hr : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hq
    have h := manuscript_atanJ_nonneg_interval (t : ℝ) hr
      (by simpa only [abs_of_nonneg hr] using ht)
    rw [manuscriptAtanInterval, ite_eq_left hq]
    change (barrierAtanJRat t : ℝ) ≤ Real.arctan (t : ℝ) ∧
      Real.arctan (t : ℝ) ≤ ((barrierAtanJRat t + |t| ^ 49 / 49 : ℚ) : ℝ)
    push_cast
    rw [barrierAtanJRat_cast, abs_of_nonneg hr]
    exact h
  · have hr : (t : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hq)
    have h := manuscript_atanJ_neg_interval (t : ℝ) hr ht
    rw [manuscriptAtanInterval, ite_eq_right hq]
    change ((barrierAtanJRat t - |t| ^ 49 / 49 : ℚ) : ℝ) ≤ Real.arctan (t : ℝ) ∧
      Real.arctan (t : ℝ) ≤ (barrierAtanJRat t : ℝ)
    push_cast
    rw [barrierAtanJRat_cast]
    exact h

theorem manuscript_pi_quarter_interval :
    Real.pi / 4 ∈ Set.Icc (manuscriptPiQuarterInterval.1 : ℝ)
      (manuscriptPiQuarterInterval.2 : ℝ) := by
  have h := manuscript_interval_add
    (manuscript_atan_interval (1 / 2) (by norm_num))
    (manuscript_atan_interval (1 / 3) (by norm_num))
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  rw [barrier_atan_half_add_third] at h
  exact h

theorem manuscript_arg_interval (k : ℤ) (t : ℚ) (ht : |(t : ℝ)| ≤ 1 / 2) :
    (k : ℝ) * (Real.pi / 4) + Real.arctan (t : ℝ) ∈
      Set.Icc ((manuscriptArgInterval k t).1 : ℝ) ((manuscriptArgInterval k t).2 : ℝ) := by
  have h := manuscript_interval_add
    (manuscript_interval_scale (k : ℚ) manuscript_pi_quarter_interval)
    (manuscript_atan_interval t ht)
  simpa only [Rat.cast_intCast, manuscriptArgInterval] using h

theorem manuscript_complex_arg_interval (k : ℤ) (z : ℂ) (r s : ℚ)
    (hrot : barrierOctantRotate k z = ⟨(r : ℝ), (s : ℝ)⟩)
    (hr : (0 : ℝ) < (r : ℝ)) (hs : |(s : ℝ)| ≤ (r : ℝ) / 2)
    (hk : |k| ≤ 4) (hpos : k = 4 → (s : ℝ) ≤ 0)
    (hneg : k = -4 → (0 : ℝ) < (s : ℝ)) :
    Complex.arg z ∈ Set.Icc ((manuscriptArgInterval k (s / r)).1 : ℝ)
      ((manuscriptArgInterval k (s / r)).2 : ℝ) := by
  rw [barrierComplexArg_octant_rational k z (r : ℝ) (s : ℝ) hrot hr hs hk hpos hneg]
  have ht : |((s / r : ℚ) : ℝ)| ≤ 1 / 2 := by
    rw [Rat.cast_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    linarith
  simpa only [Rat.cast_div] using manuscript_arg_interval k (s / r) ht

end

def manuscriptLogHErrorRat (y : ℚ) : ℚ :=
  2 * ((y - 1) / (y + 1)) ^ 37 /
    (37 * (1 - ((y - 1) / (y + 1)) ^ 2))

def manuscriptLogHInterval (y : ℚ) : ℚ × ℚ :=
  (barrierLogHRat y, barrierLogHRat y + manuscriptLogHErrorRat y)

def manuscriptScaledLogInterval (m : ℤ) (y : ℚ) : ℚ × ℚ :=
  manuscriptIntervalAdd (manuscriptIntervalScale (m : ℚ) (manuscriptLogHInterval 2))
    (manuscriptLogHInterval y)

theorem manuscript_logH_interval (y : ℚ)
    (hy : (y : ℝ) ∈ Set.Icc (1 : ℝ) 2) :
    Real.log (y : ℝ) ∈ Set.Icc ((manuscriptLogHInterval y).1 : ℝ)
      ((manuscriptLogHInterval y).2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := barrier_logH_remainder hy
  change (barrierLogHRat y : ℝ) ≤ Real.log (y : ℝ) ∧
    Real.log (y : ℝ) ≤ ((barrierLogHRat y + manuscriptLogHErrorRat y : ℚ) : ℝ)
  rw [Rat.cast_add, barrierLogHRat_cast]
  have he : (manuscriptLogHErrorRat y : ℝ) =
      2 * (((y : ℝ) - 1) / ((y : ℝ) + 1)) ^ 37 /
        (37 * (1 - (((y : ℝ) - 1) / ((y : ℝ) + 1)) ^ 2)) := by
    unfold manuscriptLogHErrorRat
    push_cast
    rfl
  rw [he]
  constructor <;> linarith

theorem manuscript_scaled_log_interval (m : ℤ) (y : ℚ)
    (hy : (y : ℝ) ∈ Set.Icc (1 : ℝ) 2) :
    Real.log ((2 : ℝ) ^ m * (y : ℝ)) ∈
      Set.Icc ((manuscriptScaledLogInterval m y).1 : ℝ)
        ((manuscriptScaledLogInterval m y).2 : ℝ) := by
  have htwo := manuscript_logH_interval 2 (by norm_num)
  have hscaled := manuscript_interval_scale (m : ℚ) htwo
  have h := manuscript_interval_add hscaled (manuscript_logH_interval y hy)
  have hypos : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (by norm_num) hy.1
  rw [Real.log_mul (zpow_ne_zero m (by norm_num)) (ne_of_gt hypos), Real.log_zpow]
  simpa only [Rat.cast_intCast, Rat.cast_ofNat, manuscriptScaledLogInterval] using h

theorem manuscript_fixed_log_interval {s : ℝ} (m : ℤ) (y : ℚ)
    (hs : s = (2 : ℝ) ^ m * (y : ℝ))
    (hy : (y : ℝ) ∈ Set.Icc (1 : ℝ) 2) :
    Real.log s ∈ Set.Icc ((manuscriptScaledLogInterval m y).1 : ℝ)
      ((manuscriptScaledLogInterval m y).2 : ℝ) := by
  rw [hs]
  exact manuscript_scaled_log_interval m y hy

def manuscriptWeightedComplexLogInterval (c d : ℚ) (m k : ℤ) (y t : ℚ) : ℚ × ℚ :=
  manuscriptIntervalAdd
    (manuscriptIntervalScale (c / 2) (manuscriptScaledLogInterval m y))
    (manuscriptIntervalScale (-d) (manuscriptArgInterval k t))

theorem manuscript_weighted_complex_log_interval
    (c d : ℚ) (z : ℂ) (m k : ℤ) (y r s : ℚ)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * (y : ℝ))
    (hy : (y : ℝ) ∈ Set.Icc (1 : ℝ) 2)
    (hrot : barrierOctantRotate k z = ⟨(r : ℝ), (s : ℝ)⟩)
    (hr : (0 : ℝ) < (r : ℝ)) (hs : |(s : ℝ)| ≤ (r : ℝ) / 2)
    (hk : |k| ≤ 4) (hpos : k = 4 → (s : ℝ) ≤ 0)
    (hneg : k = -4 → (0 : ℝ) < (s : ℝ)) :
    (barrierComplex c d * Complex.log z).re ∈
      Set.Icc ((manuscriptWeightedComplexLogInterval c d m k y (s / r)).1 : ℝ)
        ((manuscriptWeightedComplexLogInterval c d m k y (s / r)).2 : ℝ) := by
  have hl := manuscript_scaled_log_interval m y hy
  have ha := manuscript_complex_arg_interval k z r s hrot hr hs hk hpos hneg
  have h := manuscript_interval_add (manuscript_interval_scale (c / 2) hl)
    (manuscript_interval_scale (-d) ha)
  have he : (barrierComplex c d * Complex.log z).re =
      ((c / 2 : ℚ) : ℝ) * Real.log ((2 : ℝ) ^ m * (y : ℝ)) +
        ((-d : ℚ) : ℝ) * Complex.arg z := by
    rw [Complex.mul_re, Complex.log_im, barrierComplexLog_re, hnorm]
    simp only [barrierComplex, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
    ring
  rw [he]
  exact h

def manuscriptP00NormLogArg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptP00NormLogTerm : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptP00NormLogArg).re

def manuscriptP00NormLogInterval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-5450417859769 / 625000000000000) 0 (-4) 0 (12321 / 10000) 0

private theorem manuscriptP00_arg_eq :
    manuscriptP00NormLogArg = barrierComplex (111 / 400) 0 := by
  apply Complex.ext <;> norm_num [manuscriptP00NormLogArg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptP00_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-5450417859769 / 625000000000000) 0 := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptP00_exact_interval :
    manuscriptP00NormLogTerm ∈ Set.Icc (manuscriptP00NormLogInterval.1 : ℝ)
      (manuscriptP00NormLogInterval.2 : ℝ) := by
  unfold manuscriptP00NormLogTerm
  rw [manuscriptP00_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-5450417859769 / 625000000000000) 0
    manuscriptP00NormLogArg (-4) 0 (12321 / 10000) (111 / 400) 0
  simp only [zero_div] at h
  unfold manuscriptP00NormLogInterval
  apply h
  all_goals
    try rw [manuscriptP00_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptP00_rounded_endpoints :
    (223586491308028419923301269 / 20000000000000000000000000000) ≤ manuscriptP00NormLogInterval.1 ∧
      manuscriptP00NormLogInterval.2 ≤ (2235864913080284199704102969 / 200000000000000000000000000000) := by
  simp only [manuscriptP00NormLogInterval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptP00_norm_log_enclosure :
    manuscriptP00NormLogTerm ∈ Set.Icc ((223586491308028419923301269 / 20000000000000000000000000000) : ℝ) ((2235864913080284199704102969 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((223586491308028419923301269 / 20000000000000000000000000000) : ℝ) ≤ (manuscriptP00NormLogInterval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptP00_rounded_endpoints.1
  have hhi : (manuscriptP00NormLogInterval.2 : ℝ) ≤ ((2235864913080284199704102969 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptP00_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptP00_exact_interval.1,
    manuscriptP00_exact_interval.2.trans hhi⟩

def manuscriptNormP0_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP0_1Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP0_1Arg).re

def manuscriptNormP0_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP0_1_arg_eq : manuscriptNormP0_1Arg = barrierComplex (201 / 1000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_1_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-4999594751017 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_1_exact_interval :
    manuscriptNormP0_1Term ∈ Set.Icc (manuscriptNormP0_1Interval.1 : ℝ) (manuscriptNormP0_1Interval.2 : ℝ) := by
  unfold manuscriptNormP0_1Term
  rw [manuscriptNormP0_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4999594751017 / 2500000000000000) (0 / 1)
    manuscriptNormP0_1Arg (-5) (0) (40401 / 31250) (201 / 1000) (0 / 1)
  have hratio : ((0 / 1) / (201 / 1000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_1_rounded_endpoints :
    (3208640661093686383961006697 / 1000000000000000000000000000000) ≤ manuscriptNormP0_1Interval.1 ∧ manuscriptNormP0_1Interval.2 ≤ (3208640661093686384636201629 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP0_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_1_enclosure :
    manuscriptNormP0_1Term ∈ Set.Icc ((3208640661093686383961006697 / 1000000000000000000000000000000) : ℝ) ((3208640661093686384636201629 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3208640661093686383961006697 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_1_rounded_endpoints.1
  have hhi : (manuscriptNormP0_1Interval.2 : ℝ) ≤ ((3208640661093686384636201629 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_1_exact_interval.1, manuscriptNormP0_1_exact_interval.2.trans hhi⟩

def manuscriptNormP0_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP0_2Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP0_2Arg).re

def manuscriptNormP0_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP0_2_arg_eq : manuscriptNormP0_2Arg = barrierComplex (1 / 1) (-119 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_2_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_2_exact_interval :
    manuscriptNormP0_2Term ∈ Set.Icc (manuscriptNormP0_2Interval.1 : ℝ) (manuscriptNormP0_2Interval.2 : ℝ) := by
  unfold manuscriptNormP0_2Term
  rw [manuscriptNormP0_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000)
    manuscriptNormP0_2Arg (0) (-1) (54161 / 40000) (319 / 200) (81 / 200)
  have hratio : ((81 / 200) / (319 / 200) : ℚ) = (81 / 319) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_2_rounded_endpoints :
    (661358122763075158075038643 / 200000000000000000000000000000) ≤ manuscriptNormP0_2Interval.1 ∧ manuscriptNormP0_2Interval.2 ≤ (826697653453844082618353217 / 250000000000000000000000000000) := by
  simp only [manuscriptNormP0_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_2_enclosure :
    manuscriptNormP0_2Term ∈ Set.Icc ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_2_rounded_endpoints.1
  have hhi : (manuscriptNormP0_2Interval.2 : ℝ) ≤ ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_2_exact_interval.1, manuscriptNormP0_2_exact_interval.2.trans hhi⟩

def manuscriptNormP0_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP0_3Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP0_3Arg).re

def manuscriptNormP0_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319)

private theorem manuscriptNormP0_3_arg_eq : manuscriptNormP0_3Arg = barrierComplex (1 / 1) (119 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_3_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_3_exact_interval :
    manuscriptNormP0_3Term ∈ Set.Icc (manuscriptNormP0_3Interval.1 : ℝ) (manuscriptNormP0_3Interval.2 : ℝ) := by
  unfold manuscriptNormP0_3Term
  rw [manuscriptNormP0_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000)
    manuscriptNormP0_3Arg (0) (1) (54161 / 40000) (319 / 200) (-81 / 200)
  have hratio : ((-81 / 200) / (319 / 200) : ℚ) = (-81 / 319) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_3_rounded_endpoints :
    (661358122763075158075038643 / 200000000000000000000000000000) ≤ manuscriptNormP0_3Interval.1 ∧ manuscriptNormP0_3Interval.2 ≤ (826697653453844082618353217 / 250000000000000000000000000000) := by
  simp only [manuscriptNormP0_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_3_enclosure :
    manuscriptNormP0_3Term ∈ Set.Icc ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_3_rounded_endpoints.1
  have hhi : (manuscriptNormP0_3Interval.2 : ℝ) ≤ ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_3_exact_interval.1, manuscriptNormP0_3_exact_interval.2.trans hhi⟩

def manuscriptNormV12_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV12_12Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV12_12Arg).re

def manuscriptNormV12_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV12_12_arg_eq : manuscriptNormV12_12Arg = barrierComplex (30754 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_12_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_12_exact_interval :
    manuscriptNormV12_12Term ∈ Set.Icc (manuscriptNormV12_12Interval.1 : ℝ) (manuscriptNormV12_12Interval.2 : ℝ) := by
  unfold manuscriptNormV12_12Term
  rw [manuscriptNormV12_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (58419274664429 / 5000000000000000) (44630695170837 / 20000000000000000)
    manuscriptNormV12_12Arg (1) (0) (472904258 / 244140625) (30754 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (30754 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_12_rounded_endpoints :
    (988962187297497831790278377 / 125000000000000000000000000000) ≤ manuscriptNormV12_12Interval.1 ∧ manuscriptNormV12_12Interval.2 ≤ (7911697498379982655265387197 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_12_enclosure :
    manuscriptNormV12_12Term ∈ Set.Icc ((988962187297497831790278377 / 125000000000000000000000000000) : ℝ) ((7911697498379982655265387197 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((988962187297497831790278377 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_12_rounded_endpoints.1
  have hhi : (manuscriptNormV12_12Interval.2 : ℝ) ≤ ((7911697498379982655265387197 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_12_exact_interval.1, manuscriptNormV12_12_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI

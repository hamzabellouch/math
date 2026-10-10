import Mathlib

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}
noncomputable def distanceCoordinate (f : ℝ → X) (q : ℕ) (t : ℝ) : ℝ :=
  dist (f t) (denseSeq X q)

noncomputable def metricSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ⨆ q : ℕ, |deriv (distanceCoordinate f q) t|

lemma coordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (distanceCoordinate f q) := by
  change LipschitzWith K (fun t : ℝ => dist (f t) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma coordinate_deriv_bound (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ K := by
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (coordinate_lipschitz hf q)

lemma coordinate_deriv_le_speed (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ metricSpeed f t :=
  le_ciSup ⟨(K : ℝ), by rintro v ⟨r, rfl⟩; exact coordinate_deriv_bound hf r t⟩ q

lemma metricSpeed_nonneg (hf : LipschitzWith K f) (t : ℝ) : 0 ≤ metricSpeed f t :=
  (abs_nonneg _).trans (coordinate_deriv_le_speed hf 0 t)

lemma metricSpeed_le (hf : LipschitzWith K f) (t : ℝ) : metricSpeed f t ≤ K :=
  ciSup_le (fun q => coordinate_deriv_bound hf q t)

lemma measurable_metricSpeed (f : ℝ → X) : Measurable (metricSpeed f) :=
  Measurable.iSup (fun q => (measurable_deriv (distanceCoordinate f q)).abs)

lemma locallyIntegrable_metricSpeed (hf : LipschitzWith K f) :
    LocallyIntegrable (metricSpeed f) volume := by
  apply (memLp_top_of_bound (measurable_metricSpeed f).aestronglyMeasurable (K : ℝ) ?_).locallyIntegrable le_top
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg hf t)]
    exact metricSpeed_le hf t

lemma intervalIntegrable_metricSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    IntervalIntegrable (metricSpeed f) volume s t :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_metricSpeed hf).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

lemma coordinate_difference_bound (hf : LipschitzWith K f) (q : ℕ) {s t : ℝ} (hst : s ≤ t) :
    |distanceCoordinate f q t - distanceCoordinate f q s| ≤ ∫ x in s..t, metricSpeed f x := by
  have hac := (coordinate_lipschitz hf q).lipschitzOnWith.absolutelyContinuousOnInterval (a := s) (b := t)
  rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hst).trans
  apply intervalIntegral.integral_mono_on hst hac.intervalIntegrable_deriv.norm
    (intervalIntegrable_metricSpeed hf s t)
  intro x hx
  exact coordinate_deriv_le_speed hf q x

lemma distance_le_integral_speed (hf : LipschitzWith K f) {s t : ℝ} (hst : s ≤ t) :
    dist (f t) (f s) ≤ ∫ x in s..t, metricSpeed f x := by
  have hc : Continuous (fun y : X => |dist (f t) y - dist (f s) y|) :=
    ((continuous_const.dist continuous_id).sub (continuous_const.dist continuous_id)).abs
  have h := (denseRange_denseSeq X).induction_on
    (p := fun y : X => |dist (f t) y - dist (f s) y| ≤
      ∫ x in s..t, metricSpeed f x) (f s) (isClosed_le hc continuous_const)
      (fun q => coordinate_difference_bound hf q hst)
  simpa using h

noncomputable def integratedSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, metricSpeed f x

lemma distance_le_integratedSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    dist (f t) (f s) ≤ |integratedSpeed f t - integratedSpeed f s| := by
  have hi (a b : ℝ) := intervalIntegrable_metricSpeed hf a b
  have hd (a b : ℝ) : integratedSpeed f b - integratedSpeed f a =
      ∫ x in a..b, metricSpeed f x := by
    exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  rcases le_total s t with hst | hts
  · rw [hd s t, abs_of_nonneg (intervalIntegral.integral_nonneg hst
      (fun x hx => metricSpeed_nonneg hf x))]
    exact distance_le_integral_speed hf hst
  · rw [abs_sub_comm, hd t s, abs_of_nonneg (intervalIntegral.integral_nonneg hts
      (fun x hx => metricSpeed_nonneg hf x)), dist_comm]
    exact distance_le_integral_speed hf hts

def HasMetricDerivAt (f : ℝ → X) (v x : ℝ) : Prop :=
  Tendsto (fun t => dist (f t) (f x) / |t-x|) (𝓝[≠] x) (𝓝 v)

lemma abs_slope_tendsto {g : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt g d x) :
    Tendsto (fun t => |g t-g x|/|t-x|) (𝓝[≠] x) (𝓝 |d|) := by
  simpa only [slope, norm_smul, norm_inv, Real.norm_eq_abs, vsub_eq_sub, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope.norm

theorem ae_hasMetricDerivAt (hf : LipschitzWith K f) :
    ∀ᵐ x, HasMetricDerivAt f (metricSpeed f x) x := by
  have hcoords : ∀ᵐ x, ∀ q : ℕ, DifferentiableAt ℝ (distanceCoordinate f q) x := by
    rw [ae_all_iff]
    intro q
    exact (coordinate_lipschitz hf q).ae_differentiableAt_real
  have hint := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_metricSpeed hf)
  filter_upwards [hcoords, hint] with x hx hI
  have hg := abs_slope_tendsto (hI 0)
  rw [abs_of_nonneg (metricSpeed_nonneg hf x)] at hg
  change Tendsto (fun t => |integratedSpeed f t-integratedSpeed f x|/|t-x|)
    (𝓝[≠] x) (𝓝 (metricSpeed f x)) at hg
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hb : BddAbove (range (fun q : ℕ => |deriv (distanceCoordinate f q) x|)) :=
      ⟨(K : ℝ), by rintro v ⟨q, rfl⟩; exact coordinate_deriv_bound hf q x⟩
    obtain ⟨q, hq⟩ := (lt_ciSup_iff hb).mp hc
    have hd := abs_slope_tendsto (hx q).hasDerivAt
    filter_upwards [hd.eventually (eventually_gt_nhds hq)] with t ht
    exact ht.trans_le (div_le_div_of_nonneg_right
      (abs_dist_sub_le (f t) (f x) (denseSeq X q)) (abs_nonneg _))
  · intro c hc
    filter_upwards [hg.eventually (eventually_lt_nhds hc)] with t ht
    exact (div_le_div_of_nonneg_right (distance_le_integratedSpeed hf x t) (abs_nonneg _)).trans_lt ht

end SharpIntegralFillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI

import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.RadialMixture

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma gaussianKernel_scale (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianKernel m δ (δ • y) = δ⁻¹ ^ m * GaussianKernel m 1 y := by
  have he (a : ℝ) : gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (δ*a) =
      δ⁻¹ * gaussianPDFReal 0 1 a := by
    have h := gaussianPDFReal_inv_mul (μ := 0) (v := 1) hδ.ne' (δ*a)
    simp only [inv_mul_cancel_left₀ hδ.ne', mul_zero, mul_one, abs_of_pos hδ] at h
    rw [h]
    field_simp
    rfl
  unfold GaussianKernel
  simp only [PiLp.smul_apply, smul_eq_mul, one_pow]
  simp_rw [he]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma radialMixture_scale (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    RadialMixture m δ (δ*r) = δ⁻¹ * RadialMixture m 1 r := by
  unfold RadialMixture
  rw [mul_smul, gaussianKernel_scale m hδ]
  simp only [one_pow, div_one, mul_pow, inv_pow]
  field_simp

def BallAverage {m : ℕ} (ν : Measure (Space m)) (y : Space m) (r : ℝ) : ℝ :=
  (ν (Metric.ball y r)).toReal / (UnitBallVolume m * r^m)

lemma ballAverage_measurable {m : ℕ} (ν : Measure (Space m)) (y : Space m) :
    Measurable (BallAverage ν y) := by
  have h : Monotone (fun r : ℝ => ν (Metric.ball y r)) := fun r t h =>
    measure_mono (Metric.ball_subset_ball h)
  exact h.measurable.ennreal_toReal.div (by fun_prop)

lemma ballAverage_nonneg {m : ℕ} (ν : Measure (Space m)) (y : Space m) {r : ℝ}
    (hr : 0 < r) : 0 ≤ BallAverage ν y r := by
  exact div_nonneg ENNReal.toReal_nonneg (mul_nonneg (unitBallVolume_pos m).le
    (pow_nonneg hr.le _))

lemma ac_ball_eq_closedBall {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    (hν : ν ≪ volume) (y : Space m) (r : ℝ) :
    ν (Metric.ball y r) = ν (Metric.closedBall y r) := by
  have : NeZero m := ⟨by omega⟩
  apply measure_eq_measure_of_null_sdiff Metric.ball_subset_closedBall
  rw [Metric.closedBall_sdiff_ball]
  exact hν (Measure.addHaar_sphere volume y r)

lemma ae_tendsto_ballAverage {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Space m)), Tendsto (BallAverage ν y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  have : NeZero m := ⟨by omega⟩
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν volume, ν.rnDeriv_lt_top volume] with y hy hyfin
  have ht := (ENNReal.continuousAt_toReal hyfin.ne).tendsto.comp hy
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  unfold BallAverage
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_div, Measure.addHaar_closedBall_eq_addHaar_ball volume y r,
    ← ac_ball_eq_closedBall hm ν hν y r, volume_ball_eq m hm y hr,
    ENNReal.toReal_ofReal (mul_nonneg (unitBallVolume_pos m).le (pow_nonneg hr.le _))]

lemma ballAverage_bounded {m : ℕ} (ν : Measure (Space m)) [IsFiniteMeasure ν]
    (y : Space m) {f : ℝ} (hf : 0 ≤ f)
    (ht : Tendsto (BallAverage ν y) (𝓝[>] (0:ℝ)) (𝓝 f)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ‖BallAverage ν y r‖ ≤ B := by
  rcases Metric.tendsto_nhdsWithin_nhds.mp ht 1 zero_lt_one with ⟨b,hb,hnear⟩
  let C : ℝ := max (f+1) ((ν Set.univ).toReal / (UnitBallVolume m * b^m))
  refine ⟨C, le_trans (by linarith : 0 ≤ f+1) (le_max_left _ _), ?_⟩
  intro r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (ballAverage_nonneg ν y hr)]
  by_cases h : r < b
  · have he := hnear hr (by simpa [Real.dist_eq, abs_of_pos hr] using h)
    have he' : BallAverage ν y r < f+1 := by
      rw [Real.dist_eq] at he
      have := (abs_lt.mp he).2
      linarith
    exact he'.le.trans (le_max_left _ _)
  · apply le_trans ?_ (le_max_right _ _)
    unfold BallAverage
    have hvol : 0 < UnitBallVolume m := unitBallVolume_pos m
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        (measure_mono (Set.subset_univ _))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le (le_of_not_gt h) _)
        (unitBallVolume_pos m).le

lemma tendsto_radial_average {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m)) [IsFiniteMeasure ν]
    (y : Space m) {f : ℝ} (hf : 0 ≤ f)
    (ht : Tendsto (BallAverage ν y) (𝓝[>] (0:ℝ)) (𝓝 f)) :
    Tendsto (fun δ : ℝ => ∫ r in Ioi 0, RadialMixture m 1 r * BallAverage ν y (δ*r))
      (𝓝[>] (0:ℝ)) (𝓝 f) := by
  obtain ⟨B,hB,hbound⟩ := ballAverage_bounded ν y hf ht
  have hw : IntegrableOn (RadialMixture m 1) (Ioi 0) :=
    integrable_of_integral_eq_one (radialMixture_integral m hm zero_lt_one)
  have hl := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (l := 𝓝[>] (0:ℝ))
    (F := fun δ r => RadialMixture m 1 r * BallAverage ν y (δ*r))
    (f := fun r => RadialMixture m 1 r * f)
    (fun r => RadialMixture m 1 r * B)
    (Eventually.of_forall (fun δ =>
      ((radialMixture_measurable m 1).mul ((ballAverage_measurable ν y).comp
        (by fun_prop))).aestronglyMeasurable))
    (show ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ᵐ r ∂volume.restrict (Ioi 0),
      ‖RadialMixture m 1 r * BallAverage ν y (δ*r)‖ ≤ RadialMixture m 1 r * B from by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (radialMixture_nonneg m 1 hr)]
      exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hδ hr)) (radialMixture_nonneg m 1 hr))
    (hw.mul_const B) (show ∀ᵐ r ∂volume.restrict (Ioi 0),
      Tendsto (fun δ => RadialMixture m 1 r * BallAverage ν y (δ*r))
        (𝓝[>] (0:ℝ)) (𝓝 (RadialMixture m 1 r * f)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      apply Tendsto.const_mul
      apply ht.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa using ((continuous_id.mul_const r).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        change 0 < δ*r
        exact mul_pos hδ hr)
  simpa only [integral_mul_const, radialMixture_integral m hm zero_lt_one, one_mul] using hl
end MemoryPrecision


end

end OAI

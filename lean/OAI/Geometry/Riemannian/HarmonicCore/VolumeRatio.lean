import OAI.Geometry.Riemannian.HarmonicCore.PolarDensity
import OAI.Geometry.Riemannian.HarmonicCore.RadialDistance

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main

lemma polarMetric_scaled_density_tendsto {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r)
    (hf : Tendsto (fun r : ℝ ↦ f r / r) atTop (𝓝 a)) {x : E3} (hx : x ≠ 0) :
    Tendsto (fun R : ℝ ↦ Real.sqrt
      ((polarMetric ha f H hs hc hb).coeff (R • x)).det) atTop (𝓝 (a^2)) := by
  have h := (hf.comp (Tendsto.atTop_mul_const (norm_pos_iff.mpr hx) tendsto_id)).pow 2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [polarMetric_density, ite_eq_right (smul_ne_zero hR.ne' hx), norm_smul,
    Real.norm_eq_abs, abs_of_pos hR]
  rfl



theorem polarMetric_hasAVR {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r)
    (hf : Tendsto (fun r : ℝ ↦ f r / r) atTop (𝓝 a)) :
    (polarMetric ha f H hs hc hb).HasAVR (a^2) := by
  let g := polarMetric ha f H hs hc hb
  let μ : Measure E3 := volume.restrict (Metric.ball 0 1)
  let omega : ℝ := (volume (Metric.ball (0 : E3) 1)).toReal
  have homega : 0 < omega := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : E3) (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_lt_top.ne
  have hmbl : ∀ᶠ R : ℝ in atTop,
      AEStronglyMeasurable (fun x : E3 ↦ Real.sqrt (g.coeff (R • x)).det) μ := by
    exact Eventually.of_forall (fun R ↦
      (g.density_continuous.comp (continuous_const_smul R)).aestronglyMeasurable)
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ x : E3 ∂μ,
      ‖Real.sqrt (g.coeff (R • x)).det‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro R
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (polarMetric_density_bounds ha ha1 f H hs hc hb (R • x)).2
  have hlim : ∀ᵐ x : E3 ∂μ,
      Tendsto (fun R : ℝ ↦ Real.sqrt (g.coeff (R • x)).det) atTop (𝓝 (a^2)) := by
    have hne : ∀ᵐ x : E3 ∂volume, x ≠ 0 := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_of_ae hne] with x hx
    exact polarMetric_scaled_density_tendsto ha f H hs hc hb hf hx
  have hi : Integrable (fun _ : E3 ↦ (1 : ℝ)) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun _ : E3 ↦ (1 : ℝ)) hmbl hbound hi hlim
  have hconst : (∫ _x : E3, a^2 ∂μ) = omega*a^2 := by
    simp [μ, omega, integral_const, measureReal_def, smul_eq_mul]
  rw [hconst] at ht
  have ht' : Tendsto (fun R : ℝ ↦
      (∫ x : E3, Real.sqrt (g.coeff (R • x)).det ∂μ) / omega) atTop (𝓝 (a^2)) := by
    convert ht.div_const omega using 1
    field_simp
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  change (∫ x in Metric.ball (0 : E3) 1,
      Real.sqrt (g.coeff (R • x)).det) / omega =
    (g.volumeMeasure {x | g.distance 0 x < R}).toReal / (omega * R^3)
  have hball : {x : E3 | g.distance 0 x < R} = Metric.ball 0 R := by
    ext x
    simp only [Set.mem_ofPred_eq, polarMetric_distance_origin, Metric.mem_ball, dist_zero_right, g]
  rw [hball, g.volumeMeasure_apply measurableSet_ball]
  have hscale := Measure.setIntegral_comp_smul_of_pos volume
    (fun x : E3 ↦ Real.sqrt (g.coeff x).det) (Metric.ball (0 : E3) 1) hR
  rw [smul_unitBall hR.ne', Real.norm_eq_abs, abs_of_pos hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hscale
  rw [hscale]
  field_simp

end HarmonicCounterexample.Main

end

end OAI

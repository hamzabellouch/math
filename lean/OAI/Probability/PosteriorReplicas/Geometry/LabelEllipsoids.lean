import OAI.Probability.PosteriorReplicas.Gaussian.GaussianLogMoment
import OAI.Probability.PosteriorReplicas.Measures.ConstrainedDensityExpectation

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma liftLabel_norm_coordinates {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) : ‖liftLabel A y‖ = labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y) := by
  have h := pairingLift_energy hA y
  have he : labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y)^2 =
      ∑ i, (((pairingTriangular A).transpose⁻¹ *ᵥ y) i)^2 := by
    exact EuclideanSpace.real_norm_sq_eq _
  have hn : 0 ≤ labelNorm ((pairingTriangular A).transpose⁻¹ *ᵥ y) := norm_nonneg _
  change ‖liftLabel A y‖^2 = _ at h
  nlinarith [norm_nonneg (liftLabel A y)]

lemma label_closedBall_volume {k : ℕ} (r : ℝ) :
    (volume : Measure (Labels k)) {y | labelNorm y ≤ r} =
      volume (closedBall (0 : Vec k) r) := by
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (by measurability)]
  congr 1
  ext y
  simp [labelNorm, mem_closedBall, dist_zero_right]

lemma label_closedBall_scale {k : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Labels k)) {y | labelNorm y ≤ r} =
      ENNReal.ofReal (r^k) * volume {y : Labels k | labelNorm y ≤ 1} := by
  rw [label_closedBall_volume, label_closedBall_volume]
  simpa using Measure.addHaar_closedBall_mul (volume : Measure (Vec k)) (0 : Vec k) hr (by norm_num : (0:ℝ) ≤ 1)

lemma label_ellipsoid_volume {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (r : ℝ) :
    (volume : Measure (Labels k)) {y | ‖liftLabel A y‖ ≤ r} =
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ r} := by
  have hd := (pairingTriangular_det_pos hA).ne'
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := (pairingTriangular A).transpose⁻¹)
    (by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hd)
  have h := congrArg (fun μ : Measure (Labels k) => μ {y | labelNorm y ≤ r}) hm
  rw [Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) measurable_const),
    Measure.smul_apply, smul_eq_mul] at h
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv, pairingTriangular_det, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ext y
  simp only [mem_ofPred_eq, mem_preimage, Matrix.toLin'_apply, liftLabel_norm_coordinates hA]
  all_goals rfl

lemma label_ellipsoid_translate_volume {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) (r : ℝ) :
    (volume : Measure (Labels k)) {z | ‖liftLabel A (z-y)‖ ≤ r} =
      ENNReal.ofReal (gramVolume A) * volume {z : Labels k | labelNorm z ≤ r} := by
  have h := congrArg (fun μ : Measure (Labels k) => μ {z | ‖liftLabel A z‖ ≤ r})
    (map_add_right_eq_self (volume : Measure (Labels k)) (-y))
  rw [Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)] at h
  simpa only [preimage_ofPred_eq, sub_eq_add_neg, label_ellipsoid_volume hA r] using h

lemma projectedDensity_support_ellipsoid {d k : ℕ} (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) (hy : projectedDensity .spherical f A y ≠ 0) :
    ‖liftLabel A y‖ < 1 := by
  unfold projectedDensity baseDensity at hy
  split_ifs at hy with hA hy' <;> simp_all

lemma projectedDensity_support_volume {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (f : Vec d → ℝ≥0∞) :
    (volume : Measure (Labels k)) {y | projectedDensity .spherical f A y ≠ 0} ≤
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1} := by
  rw [← label_ellipsoid_volume hA 1]
  exact measure_mono (fun y hy => (projectedDensity_support_ellipsoid f A y hy).le)

lemma gaussian_integrable_gramVolume {d k : ℕ} :
    Integrable (gramVolume : Rows d k → ℝ) (gaussianRows d k) := by
  have hp : Integrable (fun A : Rows d k => ∏ i, ‖A i‖) (gaussianRows d k) :=
    Integrable.fintype_prod (fun _ => (IsGaussian.integrable_id (μ := stdGaussian (Vec d))).norm)
  apply hp.mono' (by fun_prop)
  exact ae_of_all _ (fun A => by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gramVolume A from Real.sqrt_nonneg _), gramVolume_eq_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun index _ => norm_gramSchmidt_le_norm A index))

lemma gaussian_label_support_volume_finite {d k : ℕ} (hd : 3 ≤ d) (hk : k < d)
    {f : Vec d → ℝ≥0∞} (_hf : Measurable f) :
    (∫⁻ A, (volume : Measure (Labels k)) {y | projectedDensity .spherical f A y ≠ 0}
      ∂gaussianRows d k) < ∞ := by
  apply lt_of_le_of_lt (lintegral_mono_ae (g := fun A : Rows d k =>
    ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1}) ?_) ?_
  · filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
    exact projectedDensity_support_volume hA f
  · rw [lintegral_mul_const _ (by fun_prop)]
    apply ENNReal.mul_lt_top
    · exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => Real.sqrt_nonneg _))).mp
        gaussian_integrable_gramVolume.hasFiniteIntegral
    · rw [label_closedBall_volume]
      exact measure_closedBall_lt_top

end PosteriorReplicas
end

end OAI

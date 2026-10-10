import Mathlib
import OAI.Geometry.IntegralFillings.Jacobian.Lipschitz

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace SharpIntegralFillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integrable_smooth_compact_L1_approx {f : E → ℝ} (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨p, hpc, hfp, hp, hpI⟩ := hf.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  obtain ⟨g, hg, hgc, hpg⟩ := continuous_compact_smooth_L1_approx μ hp hpc (half_pos hε)
  refine ⟨g, hg, hgc, ?_⟩
  have hgI := hg.continuous.integrable_of_hasCompactSupport (μ := μ) hgc
  have htriangle : (∫ x, ‖f x-g x‖ ∂μ) ≤
      (∫ x, (‖f x-p x‖ + ‖p x-g x‖) ∂μ) := by
    refine integral_mono_ae (hf.sub hgI).norm ((hf.sub hpI).norm.add (hpI.sub hgI).norm) ?_
    filter_upwards with x
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hadd := integral_add (hf.sub hpI).norm (hpI.sub hgI).norm
  simp only [Pi.sub_apply] at hadd
  rw [hadd] at htriangle
  linarith

end SharpIntegralFillings

namespace SharpIntegralFillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

noncomputable def coordinateJacobian {n : ℕ} (f : Fin n → E → ℝ)
    (v : Fin n → E) (x : E) : ℝ := Matrix.det (Matrix.of fun i j => fderiv ℝ (f j) x (v i))

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
lemma measurable_coordinateJacobian {n : ℕ} (f : Fin n → E → ℝ) (v : Fin n → E) :
    Measurable (coordinateJacobian f v) := by
  unfold coordinateJacobian
  simp only [Matrix.det_apply']
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma coordinateJacobian_uniform_bound {n : ℕ} (K : ℝ≥0) (v : Fin n → E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : Fin n → E → ℝ, (∀ i, LipschitzWith K (f i)) →
      ∀ x, ‖coordinateJacobian f v x‖ ≤ B := by
  let J : (Fin n → E →L[ℝ] ℝ) → ℝ := fun p => Matrix.det (Matrix.of fun i j => p j (v i))
  have hc : Continuous J := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).clm_apply continuous_const
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin n → E →L[ℝ] ℝ) K).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|, abs_nonneg _, fun f hf x => ?_⟩
  apply (hB (fun i => fderiv ℝ (f i) x) ?_).trans (le_abs_self B)
  simpa only [mem_closedBall, dist_zero_right] using
    (pi_norm_le_iff_of_nonneg K.coe_nonneg).2 (fun i => norm_fderiv_le_of_lipschitz ℝ (hf i))

omit [IsAddHaarMeasure μ] in
lemma integrable_mul_coordinateJacobian {n : ℕ} {a : E → ℝ} (ha : Integrable a μ)
    {f : Fin n → E → ℝ} {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (v : Fin n → E) : Integrable (fun x => a x * coordinateJacobian f v x) μ := by
  obtain ⟨B, _, hB⟩ := coordinateJacobian_uniform_bound K v
  refine (ha.norm.mul_const B).mono'
    (ha.aestronglyMeasurable.mul (measurable_coordinateJacobian f v).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB f hf x) (norm_nonneg _)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lipschitz_coordinate_tuple {n : ℕ} {f : Fin n → E → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) : LipschitzWith K (fun x i => f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).2
  intro i
  exact (hf i).dist_le_mul x y

lemma ae_coordinateJacobian_cons {n : ℕ} {h : E → ℝ} {g : Fin n → E → ℝ}
    {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i)) (v : Fin (n+1) → E) :
    coordinateJacobian (Fin.cons h g) v =ᵐ[μ]
      mixedJacobian h (fun x i => g i x) v := by
  have hd := (ae_all_iff.mpr (fun i => (hg i).ae_differentiableAt (μ := μ)))
  filter_upwards [hd] with x hx
  unfold coordinateJacobian mixedJacobian
  rw [fderiv_pi hx]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coordinateJacobian_cons {n : ℕ} (h : E → ℝ) (g : Fin n → E → ℝ)
    (v : Fin (n+1) → E) (x : E) :
    coordinateJacobian (Fin.cons h g) v x =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val * fderiv ℝ h x (v i) *
        coordinateJacobian g (i.removeNth v) x := by
  unfold coordinateJacobian
  rw [Matrix.det_succ_column_zero]
  rfl

lemma integral_coordinateJacobian_cons {n : ℕ} {f h : E → ℝ}
    {g : Fin n → E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {K L : ℝ≥0} (hh : LipschitzWith K h) (hg : ∀ i, LipschitzWith L (g i))
    (v : Fin (n+1) → E) :
    (∫ x, f x * coordinateJacobian (Fin.cons h g) v x ∂μ) =
      -(∫ x, h x * coordinateJacobian (Fin.cons f g) v x ∂μ) := by
  have H := integral_lipschitz_mixedJacobian_mul μ hf hfc hh (lipschitz_coordinate_tuple hg) v
  calc (∫ x, f x * coordinateJacobian (Fin.cons h g) v x ∂μ) =
      (∫ x, f x * mixedJacobian h (fun x i => g i x) v x ∂μ) := by
        apply integral_congr_ae
        filter_upwards [ae_coordinateJacobian_cons μ (h := h) hg v] with x hx
        rw [hx]
    _ = -(∫ x, h x * mixedJacobian f (fun x i => g i x) v x ∂μ) := H
    _ = -(∫ x, h x * coordinateJacobian (Fin.cons f g) v x ∂μ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_coordinateJacobian_cons μ (h := f) hg v] with x hx
        rw [hx]

end SharpIntegralFillings

namespace SharpIntegralFillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [IsAddHaarMeasure μ] in
lemma tendsto_integral_mul_uniformly_bounded {as Js : ℕ → E → ℝ}
    {A : E → ℝ} {B : ℝ}
    (hA : Integrable A μ) (ha : ∀ j, AEStronglyMeasurable (as j) μ)
    (hJ : ∀ j, AEStronglyMeasurable (Js j) μ)
    (haA : ∀ j, ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x)
    (hJB : ∀ j x, ‖Js j x‖ ≤ B)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, as j x * Js j x ∂μ) atTop (𝓝 0) := by
  have H := tendsto_integral_of_dominated_convergence (fun x => A x * B)
    (fun j => (ha j).mul (hJ j)) (hA.mul_const B)
    (fun j => by
      filter_upwards [haA j] with x hx
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul hx (hJB j x) (norm_nonneg _) ((norm_nonneg _).trans hx))
    (show ∀ᵐ x ∂μ, Tendsto (fun j => as j x * Js j x) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [halim] with x hx
      refine squeeze_zero_norm (a := fun j => ‖as j x‖ * B) ?_ ?_
      · intro j
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hJB j x) (norm_nonneg _)
      · simpa using hx.norm.mul_const B)
  simpa using H

end SharpIntegralFillings
end

end OAI

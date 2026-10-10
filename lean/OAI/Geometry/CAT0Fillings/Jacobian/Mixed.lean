import Mathlib
import OAI.Geometry.CAT0Fillings.Jacobian.ClosedForms

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

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
noncomputable def mixedJacobian {n : ℕ} (f : E → ℝ) (g : E → Fin n → ℝ)
    (v : Fin (n+1) → E) (x : E) : ℝ :=
  Matrix.det (Matrix.of (fun i => Matrix.vecCons (fderiv ℝ f x (v i))
    (fderiv ℝ g x (v i))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : Fin (n+1) → E) :
    Continuous (mixedJacobian f g v) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact (continuous_apply j).comp
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedJacobian_eq_zero_of_fderiv_eq_zero {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (v : Fin (n+1) → E) {x : E} (h : fderiv ℝ f x = 0) :
    mixedJacobian f g v x = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (0 : Fin (n+1))
  intro i
  simp [h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasCompactSupport_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : HasCompactSupport f) (v : Fin (n+1) → E) :
    HasCompactSupport (mixedJacobian f g v) := by
  apply (hf.fderiv ℝ).mono
  intro x hx
  contrapose! hx
  simpa using (mixedJacobian_eq_zero_of_fderiv_eq_zero (g := g) v (by simpa using hx))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    {x : E} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (v : Fin (n+1) → E) :
    mixedJacobian (fun y => f y * h y) g v x =
      f x * mixedJacobian h g v x + h x * mixedJacobian f g v x := by
  have hprod (i : Fin (n+1)) : fderiv ℝ (fun y => f y * h y) x (v i) =
      f x * fderiv ℝ h x (v i) + h x * fderiv ℝ f x (v i) := by
    rw [fderiv_fun_mul hf hh]
    rfl
  simp only [mixedJacobian, Matrix.det_succ_column_zero, Matrix.of_apply,
    Matrix.cons_val_zero, hprod]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.submatrix, Matrix.of_apply, Matrix.cons_val_succ]
  ring

lemma integral_smooth_mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hh : ContDiff ℝ 1 h)
    (hg : ContDiff ℝ 2 g) (v : Fin (n+1) → E) :
    (∫ x, f x * mixedJacobian h g v x ∂μ) =
      -(∫ x, h x * mixedJacobian f g v x ∂μ) := by
  have hgc : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hI₁ : Integrable (fun x => f x * mixedJacobian h g v x) μ :=
    (hf.continuous.mul (continuous_mixedJacobian hh hgc v)).integrable_of_hasCompactSupport
      hfc.mul_right
  have hI₂ : Integrable (fun x => h x * mixedJacobian f g v x) μ :=
    (hh.continuous.mul (continuous_mixedJacobian hf hgc v)).integrable_of_hasCompactSupport
      (hasCompactSupport_mixedJacobian hfc v).mul_left
  have H := integral_smooth_jacobian_eq_zero μ (hf.mul hh) hfc.mul_right hg v
  change (∫ x, mixedJacobian (fun y => f y * h y) g v x ∂μ) = 0 at H
  simp_rw [mixedJacobian_mul (hf.differentiable one_ne_zero _) (hh.differentiable one_ne_zero _)] at H
  rw [integral_add hI₁ hI₂] at H
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_mixedJacobian_bound {n : ℕ} (K L : ℝ) (v : Fin (n+1) → E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : E → ℝ) (g : E → Fin n → ℝ) x,
      ‖fderiv ℝ f x‖ ≤ K → ‖fderiv ℝ g x‖ ≤ L →
      ‖mixedJacobian f g v x‖ ≤ B := by
  let D := (E →L[ℝ] ℝ) × (E →L[ℝ] (Fin n → ℝ))
  let J : D → ℝ := fun p => Matrix.det (Matrix.of fun i => Matrix.vecCons (p.1 (v i)) (p.2 (v i)))
  have hc : Continuous J := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    exact (continuous_fst.clm_apply continuous_const).matrixVecCons
      (continuous_snd.clm_apply continuous_const)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : E →L[ℝ] ℝ) K).prod
    (isCompact_closedBall (0 : E →L[ℝ] (Fin n → ℝ)) L)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|, abs_nonneg _, fun f g x hf hg => ?_⟩
  apply (hB (fderiv ℝ f x, fderiv ℝ g x) ?_).trans (le_abs_self B)
  exact ⟨by simpa using hf, by simpa using hg⟩

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
lemma aestronglyMeasurable_mixedJacobian {n : ℕ} (f : E → ℝ) (g : E → Fin n → ℝ)
    (v : Fin (n+1) → E) : AEStronglyMeasurable (mixedJacobian f g v) μ := by
  have h : Measurable (mixedJacobian f g v) := by
    unfold mixedJacobian
    simp only [Matrix.det_apply']
    fun_prop
  exact h.aestronglyMeasurable

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] [BorelSpace E] in
lemma ae_tendsto_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    {fs : ℕ → E → ℝ} {gs : ℕ → E → Fin n → ℝ}
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (fs j) x) atTop (𝓝 (fderiv ℝ f x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (gs j) x) atTop (𝓝 (fderiv ℝ g x)))
    (v : Fin (n+1) → E) :
    ∀ᵐ x ∂μ, Tendsto (fun j => mixedJacobian (fs j) (gs j) v x) atTop
      (𝓝 (mixedJacobian f g v x)) := by
  filter_upwards [hf, hg] with x hx hy
  have H : Continuous (fun p : (E →L[ℝ] ℝ) × (E →L[ℝ] (Fin n → ℝ)) =>
      Matrix.det (Matrix.of fun i => Matrix.vecCons (p.1 (v i)) (p.2 (v i)))) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    exact (continuous_fst.clm_apply continuous_const).matrixVecCons
      (continuous_snd.clm_apply continuous_const)
  exact H.continuousAt.tendsto.comp (hx.prodMk_nhds hy)

omit [IsAddHaarMeasure μ] in
lemma tendsto_integral_weighted_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    {fs : ℕ → E → ℝ} {gs : ℕ → E → Fin n → ℝ} {as : ℕ → E → ℝ} {a A : E → ℝ}
    {K L : ℝ} (hK : ∀ j x, ‖fderiv ℝ (fs j) x‖ ≤ K)
    (hL : ∀ j x, ‖fderiv ℝ (gs j) x‖ ≤ L)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (fs j) x) atTop (𝓝 (fderiv ℝ f x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (gs j) x) atTop (𝓝 (fderiv ℝ g x)))
    (ha : ∀ j, AEStronglyMeasurable (as j) μ)
    (hac : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 (a x)))
    (hA : Integrable A μ) (haA : ∀ j, ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x)
    (v : Fin (n+1) → E) :
    Tendsto (fun j => ∫ x, as j x * mixedJacobian (fs j) (gs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * mixedJacobian f g v x ∂μ)) := by
  obtain ⟨B, _, hB⟩ := exists_mixedJacobian_bound K L v
  apply tendsto_integral_of_dominated_convergence (fun x => A x * B)
  · exact fun j => (ha j).mul (aestronglyMeasurable_mixedJacobian μ _ _ _)
  · exact hA.mul_const B
  · intro j
    filter_upwards [haA j] with x hx
    rw [norm_mul]
    exact mul_le_mul hx (hB _ _ _ (hK j x) (hL j x)) (norm_nonneg _) ((norm_nonneg _).trans hx)
  · filter_upwards [hac, ae_tendsto_mixedJacobian μ hf hg v] with x hx hy
    exact hx.mul hy

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma uniformly_bounded_lipschitz_on_compact {fs : ℕ → E → ℝ} {f : E → ℝ}
    {K : ℝ≥0} (hK : ∀ j, LipschitzWith K (fs j))
    (hf : Tendsto (fun j => fs j 0) atTop (𝓝 (f 0))) {s : Set E} (hs : IsCompact s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ s → ‖fs j x‖ ≤ B := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hf).exists_norm_le
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  refine ⟨K * |R| + |C|, by positivity, fun j x hx => ?_⟩
  calc ‖fs j x‖ ≤ ‖fs j x - fs j 0‖ + ‖fs j 0‖ := norm_le_norm_sub_add _ _
    _ ≤ K * ‖x‖ + C := by
      gcongr
      · simpa [dist_eq_norm] using (hK j).dist_le_mul x 0
      · exact hC _ (mem_range_self j)
    _ ≤ K * |R| + |C| := by gcongr; exact (hR x hx).trans (le_abs_self R); exact le_abs_self C

end CAT0Fillings

open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

end

end OAI

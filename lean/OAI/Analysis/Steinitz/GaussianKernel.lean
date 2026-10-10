import OAI.Analysis.Steinitz.Survival

namespace OAI

/-! Diagonal Gaussian kernels and their densities. -/

section

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel

variable {ι : Type*} [Fintype ι]

noncomputable def diagonalLaw (v : ι → ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun i => gaussianReal 0 (v i))).map (toLp 2)

instance (v : ι → ℝ≥0) : IsProbabilityMeasure (diagonalLaw v) :=
  by
  unfold diagonalLaw
  infer_instance

noncomputable def density (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 (v i) (x i)

lemma density_nonneg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : 0 ≤ density v x := by
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i)

lemma density_continuous (v : ι → ℝ≥0) : Continuous (density v) := by
  unfold density gaussianPDFReal
  fun_prop

lemma pi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (Measure.pi fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      ((show Integrable (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 (v i) (x i)) volume from
        by simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))).restrict)
      (ae_of_all _ fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i))),
    volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 (v i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (hv i) (s i)).symm

lemma diagonalLaw_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalLaw v = volume.withDensity (fun x => ENNReal.ofReal (density v x)) := by
  apply Measure.ext
  intro s hs
  rw [diagonalLaw, Measure.map_apply (PiLp.volume_preserving_toLp ι).measurable hs,
    pi_density v hv, withDensity_apply _ (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    ← lintegral_indicator hs]
  have he (x : ι → ℝ) :
      ((toLp 2) ⁻¹' s).indicator (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) x =
      s.indicator (fun x => ENNReal.ofReal (density v x)) (toLp 2 x) := by
    by_cases hx : toLp 2 x ∈ s <;> simp [hx, density]
  simp_rw [he]
  exact (PiLp.volume_preserving_toLp ι).lintegral_comp
    ((density_continuous v).measurable.ennreal_ofReal.indicator hs)

lemma density_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (x : EuclideanSpace ℝ ι) :
    0 < density v x := by
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 (v i) (x i) (hv i)

lemma density_neg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v (-x) = density v x := by
  unfold density
  apply Finset.prod_congr rfl
  intro i _
  simp [gaussianPDFReal]

lemma density_le_zero (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v x ≤ density v 0 := by
  unfold density
  apply Finset.prod_le_prod₀
  · intro i _
    exact gaussianPDFReal_nonneg _ _ _
  · intro i _
    simp only [gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, Real.exp_zero, mul_one]
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma charFun_diagonalLaw (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) :
    charFun (diagonalLaw v) ξ = (Real.exp (-(∑ i, (v i : ℝ)*(ξ i)^2)/2) : ℂ) := by
  rw [diagonalLaw, charFun_pi]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Finset.sum_neg_distrib]
  rw [← Finset.sum_div, neg_div]

section Scale
variable [DecidableEq ι]

noncomputable def scaleMap (v : ι → ℝ≥0) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ)))

lemma scaleMap_apply (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) (i : ι) :
    scaleMap v x i = Real.sqrt (v i : ℝ) * x i := by
  change (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ))).mulVec x.ofLp i = _
  simp only [Matrix.mulVec_diagonal]

lemma stdGaussian_map_scale (v : ι → ℝ≥0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v) = diagonalLaw v := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (scaleMap v).measurable
    (PiLp.volume_preserving_toLp ι).measurable]
  have he : (scaleMap v) ∘ (toLp 2) =
      (toLp 2) ∘ (fun x : ι → ℝ => fun i => Real.sqrt (v i : ℝ)*x i) := by
    ext x i
    exact scaleMap_apply v (toLp 2 x) i
  rw [he, ← Measure.map_map (PiLp.volume_preserving_toLp ι).measurable (by fun_prop),
    Measure.pi_map_pi (f := fun i (x : ℝ) => Real.sqrt (v i : ℝ)*x)
      (fun i => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  apply congrArg Measure.pi
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (v i).coe_nonneg]

end Scale

end GaussianKernel
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma density_exp (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density v x = density v 0 * Real.exp (-(∑ i, (x i)^2 / (2*(v i : ℝ)))) := by
  simp only [density, gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero, mul_one,
    Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]

end GaussianKernel

end

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma density_integrable (v : ι → ℝ≥0) : Integrable (density v) := by
  apply ((PiLp.volume_preserving_toLp ι).integrable_comp
    (density_continuous v).aestronglyMeasurable).mp
  change Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal 0 (v i) (x i))
  simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

lemma stdGaussian_eq_density : stdGaussian (EuclideanSpace ℝ ι) =
    volume.withDensity (fun x => ENNReal.ofReal (density (fun _ : ι => 1) x)) := by
  rw [← diagonalLaw_density (fun _ : ι => 1) (fun _ => by simp)]
  exact map_pi_eq_stdGaussian.symm

lemma linear_image_density (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) :
    (stdGaussian (EuclideanSpace ℝ ι)).map e S =
      ENNReal.ofReal (∫ x in S, |e.symm.toContinuousLinearMap.det| *
        density (fun _ => 1) (e.symm x)) := by
  rw [stdGaussian_eq_density]
  exact e.symm.toHomeomorph.toMeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    volume hS (ae_of_all _ fun _ _ => density_nonneg _ _) (density_integrable _).integrableOn
    (fun x _ => e.symm.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)

end GaussianKernel

end

end OAI

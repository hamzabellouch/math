import OAI.Probability.SLE.Stochastic.PlanarKernelMean

namespace OAI

/-! Measurability and boundedness of the planar Gaussian averaging operator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma planarGaussianMean_eq_integral (δ : ℝ≥0) (f : ℝ×ℝ → ℝ)
    (hf : Continuous f) (K : ℝ≥0) (hb : ∀ z, |f z|≤K) (z : ℝ×ℝ) :
    planarGaussianMean δ f z.1 z.2 =
      ∫ y, f (z+y) ∂(gaussianReal 0 δ).prod (gaussianReal 0 δ) := by
  have hi : Integrable (fun y : ℝ×ℝ => f (z+y))
      ((gaussianReal 0 δ).prod (gaussianReal 0 δ)) :=
    Integrable.of_bound (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable K
      (Eventually.of_forall fun y => by
        simpa only [Function.comp_apply,Pi.add_apply,id_eq,Real.norm_eq_abs] using hb (z+y))
  exact (integral_prod_symm _ hi).symm

lemma planarGaussianMean_measurable (δ : ℝ≥0) (f : ℝ×ℝ → ℝ)
    (hf : Continuous f) (K : ℝ≥0) (hb : ∀ z, |f z|≤K) :
    Measurable (fun z : ℝ×ℝ => planarGaussianMean δ f z.1 z.2) := by
  simp_rw [planarGaussianMean_eq_integral δ f hf K hb]
  have hm : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => f (p.1+p.2)) :=
    hf.measurable.comp (measurable_fst.add measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma planarGaussianMean_bound (δ : ℝ≥0) (f : ℝ×ℝ → ℝ)
    (hf : Continuous f) (K : ℝ≥0) (hb : ∀ z, |f z|≤K) (z : ℝ×ℝ) :
    |planarGaussianMean δ f z.1 z.2|≤K := by
  rw [planarGaussianMean_eq_integral δ f hf K hb]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := (gaussianReal 0 δ).prod (gaussianReal 0 δ))
      (f := fun y => f (z+y)) (C := (K:ℝ))
      (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb (z+y))

end SLEExactGauge

end

end OAI

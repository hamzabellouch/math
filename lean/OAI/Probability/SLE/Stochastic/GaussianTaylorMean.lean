import OAI.Probability.SLE.BrownianGenerators

namespace OAI

/-! A scalar Gaussian Taylor estimate with finite derivative bounds for
the planar Brownian harmonic-mean argument. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma gaussian_second_taylor_integral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (K : ℝ≥0)
    (hbound : ∀ x j, j ≤ 3 → |iteratedDeriv j f x| ≤ K)
    (δ : ℝ≥0) (x : ℝ) :
    |(∫ y, f (x+y) ∂gaussianReal 0 δ)-f x-
      (1/2:ℝ)*(δ:ℝ)*iteratedDeriv 2 f x| ≤
      (K:ℝ)*(δ:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 3 := by
  let μ := gaussianReal 0 δ
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hμ : HasLaw (fun y : ℝ => y) μ μ := ⟨measurable_id.aemeasurable, by simp⟩
  have hi : Integrable (fun y => f (x+y)) μ := by
    apply Integrable.of_bound (hf.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable K
    filter_upwards [] with y
    simpa only [Function.comp_apply,Pi.add_apply,id_eq,Real.norm_eq_abs,iteratedDeriv_zero]
      using hbound (x+y) 0 (by decide)
  have hyi : Integrable (fun y : ℝ => y) μ := hμ.hasGaussianLaw.integrable
  have hysi : Integrable (fun y : ℝ => y^2) μ := hμ.hasGaussianLaw.memLp_two.integrable_sq
  have hlin : (∫ y : ℝ, deriv f x*y ∂μ)=0 := by
    rw [integral_const_mul]
    simp [μ]
  have hquad : (∫ y : ℝ, (1/2:ℝ)*iteratedDeriv 2 f x*y^2 ∂μ) =
      (1/2:ℝ)*iteratedDeriv 2 f x*(δ:ℝ) := by
    rw [integral_const_mul,gaussian_square_integral]
  let R (y : ℝ) := f (x+y)-f x-deriv f x*y-(1/2:ℝ)*iteratedDeriv 2 f x*y^2
  have hRi : Integrable R μ :=
    ((hi.sub (integrable_const _)).sub (hyi.const_mul _)).sub (hysi.const_mul _)
  have hR : ∀ y, |R y| ≤ (K:ℝ)*|y|^3 :=
    fun y => real_second_taylor_bound hf K (fun z => hbound z 3 (by decide)) x y
  have he : (∫ y, R y ∂μ) = (∫ y, f (x+y) ∂μ)-f x-
      (1/2:ℝ)*(δ:ℝ)*iteratedDeriv 2 f x := by
    have hci : Integrable (fun _ : ℝ => f x) μ := integrable_const _
    have hli : Integrable (fun y => deriv f x*y) μ := hyi.const_mul _
    have hqi : Integrable (fun y => (1/2:ℝ)*iteratedDeriv 2 f x*y^2) μ := hysi.const_mul _
    have h0i : Integrable (fun y => f (x+y)-f x) μ := hi.sub hci
    have h1i : Integrable (fun y => f (x+y)-f x-deriv f x*y) μ := h0i.sub hli
    dsimp only [R]
    rw [integral_sub h1i hqi,integral_sub h0i hli,integral_sub hi hci,hlin,hquad]
    simp only [integral_const,probReal_univ,one_smul,sub_zero]
    ring
  rw [← he]
  calc
    |∫ y, R y ∂μ| ≤ ∫ y, |R y| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) R
    _ ≤ ∫ y, (K:ℝ)*|y|^3 ∂μ := integral_mono hRi.abs
      ((gaussian_abs_moment_integrable hμ 3 (by decide)).const_mul _) hR
    _ = (K:ℝ)*(δ:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 3 := by
      rw [integral_const_mul,gaussian_abs_cube hμ]
      ring

end SLEExactGauge

end

end OAI

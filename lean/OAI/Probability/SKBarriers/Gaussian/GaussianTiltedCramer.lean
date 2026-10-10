import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianGrowth
import OAI.Probability.SKBarriers.Gaussian.GaussianIntegration
import OAI.Probability.SKBarriers.Scalar.GrowthOperations

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem HasExpGrowth.neg_real {f : ℝ → ℝ} (hf : HasExpGrowth f) :
    HasExpGrowth (fun x => -f x) :=
  hf.congr_bound zero_le_one (fun x => by simp only [norm_neg,one_mul]; exact le_rfl)

theorem HasExpGrowth.sub_real {f g : ℝ → ℝ} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg_real

theorem HasExpGrowth.integrable_gaussianTilt {V g : ℝ → ℝ}
    (hg : HasExpGrowth g) (he : HasExpGrowth (fun x => Real.exp (V x)))
    (hV : Continuous V) (hc : Continuous g) :
    Integrable g ((gaussianReal 0 1).tilted V) := by
  rw [integrable_tilted_iff (he.integrable_gaussianMeasure (Real.continuous_exp.comp hV))]
  exact (he.smul hg).integrable_gaussianMeasure ((Real.continuous_exp.comp hV).smul hc)

theorem HasExpGrowth.memLp_two_gaussianTilt {V g : ℝ → ℝ}
    (hg : HasExpGrowth g) (he : HasExpGrowth (fun x => Real.exp (V x)))
    (hV : Continuous V) (hc : Continuous g) :
    MemLp g 2 ((gaussianReal 0 1).tilted V) := by
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  simpa only [pow_two] using (hg.mul hg).integrable_gaussianTilt he hV (hc.mul hc)

theorem gaussian_tilted_stein_growth {V V' g g' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : HasExpGrowth (fun x => Real.exp (V x)))
    (heV : HasExpGrowth V') (heg : HasExpGrowth g) (heg' : HasExpGrowth g')
    (hcV : Continuous V') (hcg' : Continuous g') :
    (∫ x, x*g x ∂(gaussianReal 0 1).tilted V)=
      (∫ x, g' x ∂(gaussianReal 0 1).tilted V)+
        ∫ x, g x*V' x ∂(gaussianReal 0 1).tilted V := by
  have hcV0 := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have hcg := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hce := Real.continuous_exp.comp hcV0
  have hx : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  apply gaussian_tilted_stein _ _ _ _ hV hg
  · exact (heg.mul he).integrable_gaussianMeasure (hcg.mul hce)
  · exact (heg'.mul he).integrable_gaussianMeasure (hcg'.mul hce)
  · exact ((heg.mul heV).mul he).integrable_gaussianMeasure ((hcg.mul hcV).mul hce)
  · exact (hx.mul (heg.mul he)).integrable_gaussianMeasure (continuous_id.mul (hcg.mul hce))

theorem cramer_of_score {μ : Measure ℝ} [IsProbabilityMeasure μ] {g S : ℝ → ℝ}
    (hg : MemLp g 2 μ) (hS : MemLp S 2 μ) {d : ℝ}
    (hmean : (∫ x, S x ∂μ)=0) (hsecond : (∫ x, S x^2 ∂μ)≤1)
    (hcov : (∫ x, g x*S x ∂μ)=d) :
    d^2≤(∫ x, g x^2 ∂μ)-(∫ x, g x ∂μ)^2 := by
  have H := variance_nonneg (X:=fun x => g x-d*S x) (μ:=μ)
  rw [variance_fun_sub hg (hS.const_mul d),covariance_const_mul_right,
    variance_const_mul,variance_eq_sub hg,variance_eq_sub hS,covariance_eq_sub hg hS] at H
  simp only [Pi.mul_apply,Pi.pow_apply,hmean,hcov,mul_zero,sub_zero,zero_pow (by decide : 2≠0)] at H
  nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hsecond)]

theorem gaussian_tilted_cramer {V V' V'' g g' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : HasExpGrowth (fun x => Real.exp (V x)))
    (heV : HasExpGrowth V') (heV' : HasExpGrowth V'')
    (heg : HasExpGrowth g) (heg' : HasExpGrowth g')
    (hcV' : Continuous V'') (hcg' : Continuous g') (hconvex : ∀ x, 0≤V'' x) :
    (∫ x, g' x ∂(gaussianReal 0 1).tilted V)^2≤
      (∫ x, g x^2 ∂(gaussianReal 0 1).tilted V)-
        (∫ x, g x ∂(gaussianReal 0 1).tilted V)^2 := by
  let μ := (gaussianReal 0 1).tilted V
  have hcV := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have hcV1 := continuous_iff_continuousAt.mpr (fun x => (hV' x).continuousAt)
  have hcg := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted (he.integrable_gaussianMeasure (Real.continuous_exp.comp hcV))
  have hx : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hconst (c : ℝ) : HasExpGrowth (fun _ : ℝ => c) :=
    HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  let S : ℝ → ℝ := fun x => x-V' x
  have hs : HasExpGrowth S := hx.sub_real heV
  have hcS : Continuous S := continuous_id.sub hcV1
  have hS' (x : ℝ) : HasDerivAt S (1-V'' x) x := (hasDerivAt_id x).sub (hV' x)
  have hi (f : ℝ → ℝ) (hf : HasExpGrowth f) (hc : Continuous f) : Integrable f μ :=
    hf.integrable_gaussianTilt he hcV hc
  have hmean : (∫ x, S x ∂μ)=0 := by
    have H := gaussian_tilted_stein_growth hV (fun x => hasDerivAt_const x (1:ℝ)) he heV
      (hconst 1) (hconst 0) hcV1 continuous_const
    simp only [mul_one,one_mul,integral_zero,zero_add] at H
    rw [integral_sub (hi _ hx continuous_id) (hi _ heV hcV1),H,sub_self]
  have hscore : (∫ x, S x^2 ∂μ)=1-∫ x, V'' x ∂μ := by
    have H := gaussian_tilted_stein_growth hV hS' he heV hs
      ((hconst 1).sub_real heV') hcV1 (continuous_const.sub hcV')
    have HE (x : ℝ) : S x^2=x*S x-S x*V' x := by dsimp [S]; ring
    simp_rw [HE]
    rw [integral_sub (hi _ (hx.mul hs) (continuous_id.mul hcS))
      (hi _ (hs.mul heV) (hcS.mul hcV1)),H,add_sub_cancel_right,
      integral_sub (integrable_const 1) (hi _ heV' hcV'),integral_const,probReal_univ,one_smul]
  have hsecond : (∫ x, S x^2 ∂μ)≤1 := by
    rw [hscore]
    have HP : 0≤∫ x, V'' x ∂μ := integral_nonneg hconvex
    linarith
  have hcov : (∫ x, g x*S x ∂μ)=∫ x, g' x ∂μ := by
    have H := gaussian_tilted_stein_growth hV hg he heV heg heg' hcV1 hcg'
    have HE (x : ℝ) : g x*S x=x*g x-g x*V' x := by dsimp [S]; ring
    simp_rw [HE]
    rw [integral_sub (hi _ (hx.mul heg) (continuous_id.mul hcg))
      (hi _ (heg.mul heV) (hcg.mul hcV1)),H,add_sub_cancel_right]
  exact cramer_of_score (heg.memLp_two_gaussianTilt he hcV hcg)
    (hs.memLp_two_gaussianTilt he hcV hcS) hmean hsecond hcov

end SK.Analytic

end
end

end OAI

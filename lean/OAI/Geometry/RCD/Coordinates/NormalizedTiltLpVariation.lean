import OAI.Geometry.RCD.Transport.ExponentialTiltLpVariation

namespace OAI

/-! # The exact strong L² tangent to normalized density perturbations -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 def normalizedTiltLp (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) : Lp ℝ 2 μ :=
  (∫ x, Real.exp (t*g x)*r x ∂μ)⁻¹ • exponentialTiltLp μ r hg hgb t

 def normalizedTiltTangent (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) : Lp ℝ 2 μ :=
  lpMultiplier μ (boundedMultiplier μ g hg M hgb) r-(∫ x, g x*r x ∂μ) • r

 theorem normalizedTiltLp_coe (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    normalizedTiltLp μ r hg hgb t =ᵐ[μ] fun x =>
      (∫ y, Real.exp (t*g y)*r y ∂μ)⁻¹*(Real.exp (t*g x)*r x) := by
  filter_upwards [Lp.coeFn_smul (∫ x, Real.exp (t*g x)*r x ∂μ)⁻¹
    (exponentialTiltLp μ r hg hgb t),exponentialTiltLp_coe μ r hg hgb t] with x hs he
  exact hs.trans (by change _*_= _; rw [he])

 theorem normalizedTiltTangent_coe (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) :
    normalizedTiltTangent μ r hg hgb =ᵐ[μ] fun x => r x*(g x-∫ y, g y*r y ∂μ) := by
  filter_upwards [Lp.coeFn_sub (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r)
      ((∫ x, g x*r x ∂μ) • r),
    lpMultiplier_coe μ (boundedMultiplier μ g hg M hgb) r,
    boundedMultiplier_coe μ g hg M hgb,Lp.coeFn_smul (∫ x, g x*r x ∂μ) r] with x hs hv hgx hm
  change (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r-(∫ y, g y*r y ∂μ) • r) x = _
  rw [hs,Pi.sub_apply,hv,hgx,hm,Pi.smul_apply]
  change g x*r x-(∫ x, g x*r x ∂μ)*r x = _
  ring

 theorem normalizedTiltLp_zero (r : Lp ℝ 2 μ) (hm : (∫ x, r x ∂μ)=1)
    {g : X → ℝ} (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) :
    normalizedTiltLp μ r hg hgb 0=r := by
  unfold normalizedTiltLp
  simp only [zero_mul,Real.exp_zero,one_mul,hm,inv_one,one_smul,exponentialTiltLp_zero]

 theorem normalizedTiltLp_hasDerivAt_zero (r : Lp ℝ 2 μ) (hr : Integrable r μ)
    (hm : (∫ x, r x ∂μ)=1) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) :
    HasDerivAt (normalizedTiltLp μ r hg hgb) (normalizedTiltTangent μ r hg hgb) 0 := by
  have h0 : (∫ x, Real.exp ((0:ℝ)*g x)*r x ∂μ)=1 := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using hm
  have hZ := (exponential_tilt_integral_hasDerivAt_zero μ hr hg hgb).inv (by rw [h0]; norm_num)
  have hD := hZ.smul (exponentialTiltLp_hasDerivAt_zero μ r hg hgb)
  convert hD using 1
  · rfl
  · simp only [normalizedTiltTangent,Pi.inv_apply,h0,one_pow,div_one,inv_one,one_smul,exponentialTiltLp_zero,
      neg_smul,sub_eq_add_neg,add_comm]

end RegularPointCoordinates

end

end OAI

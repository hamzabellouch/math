import OAI.Geometry.RCD.Transport.ExponentialTiltVariation

namespace OAI

/-! # First variation of power entropy under normalized exponential perturbations -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 theorem normalized_tilt_power_integral {r g : X → ℝ} (hr : ∀ᵐ x ∂μ, 0 ≤ r x)
    {q t Z : ℝ} (hZ : 0 < Z) :
    (∫ x, (Z⁻¹*(Real.exp (t*g x)*r x))^q ∂μ) =
      (Z⁻¹)^q*(∫ x, Real.exp ((q*t)*g x)*(r x)^q ∂μ) := by
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  rw [Real.mul_rpow (inv_nonneg.mpr hZ.le) (mul_nonneg (Real.exp_pos _).le hx),
    Real.mul_rpow (Real.exp_pos _).le hx,←Real.exp_mul]
  rw [show (t*g x)*q=(q*t)*g x by ring]

 theorem normalized_tilt_power_hasDerivAt_zero {r g : X → ℝ}
    (hr : Integrable r μ) (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x) (hm : (∫ x, r x ∂μ)=1)
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) {q : ℝ}
    (hp : Integrable (fun x => (r x)^q) μ) :
    HasDerivAt (fun t : ℝ =>
      ∫ x, ((∫ y, Real.exp (t*g y)*r y ∂μ)⁻¹*(Real.exp (t*g x)*r x))^q ∂μ)
      (q*((∫ x, g x*(r x)^q ∂μ)-(∫ x, g x*r x ∂μ)*(∫ x, (r x)^q ∂μ))) 0 := by
  let Z := fun t : ℝ => ∫ x, Real.exp (t*g x)*r x ∂μ
  have hZ : HasDerivAt Z (∫ x, g x*r x ∂μ) 0 :=
    exponential_tilt_integral_hasDerivAt_zero μ hr hg hgb
  have hZ0 : Z 0=1 := by simpa only [Z,zero_mul,Real.exp_zero,one_mul] using hm
  have hZi := hZ.inv (by change Z 0 ≠ 0; rw [hZ0]; norm_num)
  have hZp := hZi.rpow_const (p := q) (Or.inl (by
    change (Z 0)⁻¹ ≠ 0
    rw [hZ0,inv_one]
    exact one_ne_zero))
  have hqb : ∀ x, |q*g x| ≤ (‖q‖₊*M:ℝ≥0) := by
    intro x
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg q)
  have hP := exponential_tilt_integral_hasDerivAt_zero μ hp (hg.const_mul q) hqb
  have hP' : HasDerivAt (fun t : ℝ => ∫ x, Real.exp ((q*t)*g x)*(r x)^q ∂μ)
      (q*(∫ x, g x*(r x)^q ∂μ)) 0 := by
    convert hP using 1
    · ext t
      congr 1
      ext x
      congr 2
      ring
    · rw [←integral_const_mul]
      congr 1
      ext x
      ring
  have hD := hZp.mul hP'
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), 0 < Z t :=
    hZ.continuousAt.tendsto.eventually (Ioi_mem_nhds (by rw [hZ0]; norm_num))
  have hEq : (fun t : ℝ => (Z t)⁻¹^q*(∫ x, Real.exp ((q*t)*g x)*(r x)^q ∂μ)) =ᶠ[𝓝 0]
      (fun t : ℝ => ∫ x, ((Z t)⁻¹*(Real.exp (t*g x)*r x))^q ∂μ) := by
    filter_upwards [hevent] with t ht
    exact (normalized_tilt_power_integral μ hr0 ht).symm
  have hD' : HasDerivAt (fun t : ℝ => (Z t)⁻¹^q*(∫ x, Real.exp ((q*t)*g x)*(r x)^q ∂μ))
      (q*((∫ x, g x*(r x)^q ∂μ)-(∫ x, g x*r x ∂μ)*(∫ x, (r x)^q ∂μ))) 0 := by
    convert hD using 1
    simp only [Pi.inv_apply, hZ0, inv_one, Real.one_rpow, one_pow, div_one,
      zero_mul, mul_zero, Real.exp_zero, one_mul]
    ring
  exact hD'.congr_of_eventuallyEq hEq.symm

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Metric.RadonDensityL2Bound

namespace OAI

/-! # Integral Cauchy--Schwarz from a pointwise product bound -/

open MeasureTheory

noncomputable section
namespace RegularPointCoordinates

private theorem quadratic_nonneg_of_square_bound (F G H t : ℝ)
    (hF : 0≤F) (hG : 0≤G) (hH : H^2≤F*G) : 0≤F+2*t*H+t^2*G := by
  by_cases hz : G=0
  · rw [hz,mul_zero] at hH
    have hh : H=0 := by nlinarith only [hH,sq_nonneg H]
    simpa only [hz,hh,mul_zero,add_zero] using hF
  · have hp : 0<G := lt_of_le_of_ne hG (Ne.symm hz)
    have he : G*(F+2*t*H+t^2*G)=(F*G-H^2)+(H+t*G)^2 := by ring
    have hn : 0≤G*(F+2*t*H+t^2*G) := by
      rw [he]
      exact add_nonneg (sub_nonneg.mpr hH) (sq_nonneg _)
    exact nonneg_of_mul_nonneg_right hn hp

/-- No square integrability of H is required: the pointwise product bound
and integrability of the three entries suffice. -/
theorem integral_sq_le_of_sq_le_product {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F G H : X → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hF0 : ∀ᵐ x ∂μ, 0≤F x) (hG0 : ∀ᵐ x ∂μ, 0≤G x)
    (hbound : ∀ᵐ x ∂μ, (H x)^2≤F x*G x) :
    (∫ x, H x ∂μ)^2≤(∫ x, F x ∂μ)*(∫ x, G x ∂μ) := by
  have hquad (t : ℝ) : 0≤(∫ x, G x ∂μ)*(t*t)+
      (2*(∫ x, H x ∂μ))*t+(∫ x, F x ∂μ) := by
    have hp : ∀ᵐ x ∂μ, 0≤F x+(2*t)*H x+t^2*G x := by
      filter_upwards [hF0,hG0,hbound] with x hf hg hh
      exact quadratic_nonneg_of_square_bound (F x) (G x) (H x) t hf hg hh
    have hi := integral_nonneg_of_ae hp
    have hFH : Integrable (fun x => F x+(2*t)*H x) μ := by
      simpa only [Pi.add_apply] using! hF.add (hH.const_mul (2*t))
    rw [integral_add hFH (hG.const_mul _),
      integral_add hF (hH.const_mul _),integral_const_mul,integral_const_mul] at hi
    nlinarith only [hi]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith only [hd]

end RegularPointCoordinates

end

end OAI

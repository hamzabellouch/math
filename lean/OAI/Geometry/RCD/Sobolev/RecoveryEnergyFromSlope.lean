import OAI.Geometry.RCD.Sobolev.RecoveredTestEnergy

namespace OAI

/-! # Variable pointwise gradient majorants retain their sharp integral energy bound -/

open Set MeasureTheory Filter
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem rescaled_recovery_energy_le (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {Ω : Set X} {r : ℝ} (hr : 0≤r) (w : SobolevSpace μ hQ) {G : X → ℝ}
    (hG : IntegrableOn (fun x => G x^2) Ω μ)
    (hgrad : ∀ᵐ x ∂μ.restrict Ω, r*SobolevSpace.minimalSlope μ hQ w x≤G x) :
    r^2*(μ.real Ω)⁻¹*(∫ x in Ω, localGamma μ hQ w w x ∂μ)≤
      (μ.real Ω)⁻¹*(∫ x in Ω, G x^2 ∂μ) := by
  have hp : ∀ᵐ x ∂μ.restrict Ω, r^2*localGamma μ hQ w w x≤G x^2 := by
    filter_upwards [hgrad,ae_restrict_of_ae (localGamma_self μ hQ w),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ w))]
      with x hx he hn
    rw [he]
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hr hn) hx 2
  have hi := integral_mono_ae ((localGamma_memL1 μ hQ w w).integrableOn.const_mul (r^2)) hG hp
  rw [integral_const_mul] at hi
  have hmass : 0≤μ.real Ω := ENNReal.toReal_nonneg
  have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hmass)
  simpa only [mul_assoc,mul_left_comm] using hm

end RegularPointCoordinates

end

end OAI

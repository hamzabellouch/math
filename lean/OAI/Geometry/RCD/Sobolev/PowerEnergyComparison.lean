import OAI.Geometry.RCD.Sobolev.SobolevPowerGammaIntegrable

namespace OAI

/-! # Positivity of the product energy controls the power-energy difference -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem power_energy_comparison (u v : SobolevSpace μ Q) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hu0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q u x)
    (hv0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q v x) (n : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
      localGamma μ Q v v x ∂μ)-
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^n*
      localGamma μ Q u u x ∂μ) ≤
    2*((∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
      localGamma μ Q v v x ∂μ)+
      (∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*(SobolevSpace.toLp μ Q v x)^(n+1)*
        localGamma μ Q u v x ∂μ)) := by
  let w := SobolevSpace.product μ Q u v A B
  have hpos : ∀ᵐ x ∂μ,
      0 ≤ (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
        localGamma μ Q v v x+
      (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^n*
        localGamma μ Q u u x+
      2*((SobolevSpace.toLp μ Q u x)^(n+1)*(SobolevSpace.toLp μ Q v x)^(n+1)*
        localGamma μ Q u v x) := by
    filter_upwards [localGamma_product_left μ Q u v w A B hu hv,
      localGamma_product_right μ Q v u v A B hu hv,
      localGamma_product_right μ Q u u v A B hu hv,localGamma_comm μ Q v u,
      localGamma_self μ Q w,hu0,hv0] with x hw h₁ h₂ hs hself hu0x hv0x
    change localGamma μ Q w w x = _ at hw
    have he : localGamma μ Q w w x =
        (SobolevSpace.toLp μ Q u x)^2*localGamma μ Q v v x+
        (SobolevSpace.toLp μ Q v x)^2*localGamma μ Q u u x+
        2*SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x*localGamma μ Q u v x := by
      rw [hw,h₁,h₂,hs]
      ring
    have hn := mul_nonneg (mul_nonneg (pow_nonneg hu0x n) (pow_nonneg hv0x n))
      (show 0 ≤ localGamma μ Q w w x by rw [hself]; positivity)
    rw [he] at hn
    convert hn using 1
    simp only [pow_add,pow_one,pow_two]
    ring
  have ha := sobolev_power_gamma_integrable μ Q u v v v A B hu hv (n+2) n
  have hb := sobolev_power_gamma_integrable μ Q v u u u B A hv hu (n+2) n
  have hc := sobolev_power_gamma_integrable μ Q u v u v A B hu hv (n+1) (n+1)
  have hI := integral_nonneg_of_ae hpos
  have hadd := integral_add (ha.add hb) (hc.const_mul 2)
  have hab := integral_add ha hb
  simp only [Pi.add_apply] at hadd hab
  rw [hadd,hab,integral_const_mul] at hI
  linarith only [hI]

end RegularPointCoordinates

end

end OAI

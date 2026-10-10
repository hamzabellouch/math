import OAI.Geometry.RCD.Sobolev.SupportedGammaIntegral

namespace OAI

/-! # A weighted mixed density is supported where either weak gradient is -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem supported_weighted_gamma (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) (F : X → ℝ) {A U : Set X} (hAU : A⊆U)
    (hf : ∀ᵐ x ∂μ, x∉A → SobolevSpace.toLp μ hQ f x=0) :
    (∫ x in U, F x*localGamma μ hQ f g x ∂μ)=
      ∫ x in A, F x*localGamma μ hQ f g x ∂μ := by
  have hz : ∀ᵐ x ∂μ, x∉A → F x*localGamma μ hQ f g x=0 := by
    filter_upwards [hf,localGamma_zero_on_level μ hQ f g 0] with x hx hγ hn
    rw [hγ (hx hn),mul_zero]
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero
    (hz.mono fun x hx hn => hx (fun hy => hn (hAU hy))),
    setIntegral_eq_integral_of_ae_compl_eq_zero hz]

end RegularPointCoordinates

end

end OAI

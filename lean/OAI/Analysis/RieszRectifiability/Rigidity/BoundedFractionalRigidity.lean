import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalRealComponents
import OAI.Analysis.RieszRectifiability.Foundations.BoundedDensityWeights
import OAI.Analysis.RieszRectifiability.Flatness.BoundedAffineConstant
import OAI.Analysis.RieszRectifiability.Rigidity.AffineHeightRigidity
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalHeightPairingContinuity

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap

theorem bounded_density_ae_affine_of_compact_fractional_equation (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0) :
    ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x ∂volume, f x = c + L x := by
  have hweight := bounded_density_polynomial_weight_integrable (p + 1) f hf M hb
  let T := heightTemperedDistribution volume f hf (p + 3) hweight
  have hT (g : 𝓢(Ambient (p + 1), ℂ)) : T g = ∫ x, f x • g x :=
    heightTemperedDistribution_apply volume f hf (p + 3) hweight g
  have hcompact (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) :
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 :=
    (compact_complex_fractional_equation_of_real p f hreal g hc).2
  have heq (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
      (∫ x, f x • fractionalSchwartzTest p g x) = 0 :=
    height_fractional_test_zero_on_mean_zero_tests p volume f hf hweight
      (fun g hc _ => hcompact g hc) g hg
  exact represented_fractional_height_ae_affine p f
    (bounded_measurable_locallyIntegrable volume f hf M hb) T hT heq
    (bounded_density_exterior_integrable (p + 1) f hf M hb)

theorem bounded_density_ae_constant_of_compact_fractional_equation (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M)
    (hreal : ∀ ψ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport ψ →
      Integrable (fun y => f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, f x = c := by
  obtain ⟨c, L, heq⟩ := bounded_density_ae_affine_of_compact_fractional_equation p f hf M hb hreal
  exact ⟨c, (ae_bounded_affine_is_constant f M hb c L heq).2⟩

end

end RieszRectifiability

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzPairingSeparation
import OAI.Analysis.RieszRectifiability.Rigidity.PointSupportedJetRepresentation
import OAI.Analysis.RieszRectifiability.Rigidity.JetMomentPolynomial

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap
open scoped FourierTransform

theorem point_supported_inverse_fourier_polynomial {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → (𝓕⁻ T : 𝓢'(Ambient d, ℂ)) g = 0) :
    ∃ P : MvPolynomial (Fin d) ℂ, ∀ g : 𝓢(Ambient d, ℂ),
      T g = ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x := by
  obtain ⟨N, c, hc⟩ := point_supported_distribution_jet_representation (𝓕⁻ T) hT
  refine ⟨jetMomentPolynomial c, fun g => ?_⟩
  have h := hc (𝓕 g)
  rw [TemperedDistribution.fourierInv_apply, FourierTransform.fourierInv_fourier_eq] at h
  exact h.trans (fourier_jet_sum_eq_polynomial_pairing c g)

theorem represented_fractional_height_polynomial_pairing (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ P : MvPolynomial (Fin (p + 1)) ℂ, ∀ g : 𝓢(Ambient (p + 1), ℂ),
      (∫ x, w x • g x) = ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x := by
  obtain ⟨P, hP⟩ := point_supported_inverse_fourier_polynomial T
    (fun g hc hz => represented_height_inverse_fourier_annihilates_away_zero p w T hT heq g hc hz)
  exact ⟨P, fun g => (hT g).symm.trans (hP g)⟩

theorem represented_fractional_height_ae_polynomial (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : MeasureTheory.LocallyIntegrable w)
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ P : MvPolynomial (Fin (p + 1)) ℂ,
      ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  obtain ⟨P, hP⟩ := represented_fractional_height_polynomial_pairing p w T hT heq
  exact ⟨P, real_height_ae_eq_polynomial_of_pairings w hw P hP⟩

end

end RieszRectifiability

end OAI

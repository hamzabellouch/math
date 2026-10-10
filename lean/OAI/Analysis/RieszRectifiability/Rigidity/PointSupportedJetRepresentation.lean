import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.PointSupportedFiniteJet
import OAI.Analysis.RieszRectifiability.Rigidity.SchwartzJetCoordinates
import OAI.Analysis.RieszRectifiability.Kernel.LinearCoordinateFactorization

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap
open scoped FourierTransform

theorem point_supported_distribution_jet_representation {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∃ c : JetCoordinateIndex d N → ℂ, ∀ g : 𝓢(Ambient d, ℂ),
      T g = ∑ i, c i * iteratedFDeriv ℝ i.1.val g 0
        (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) := by
  classical
  obtain ⟨N, hN⟩ := point_supported_distribution_finite_jet T hT
  have hker : ∀ g, schwartzJetCoordinates d N g = 0 → T g = 0 := by
    intro g hg
    have heq : schwartzJetCoordinates d N g = schwartzJetCoordinates d N 0 :=
      hg.trans (map_zero _).symm
    have hh := hN g 0 ((schwartzJetCoordinates_eq_iff d N g 0).mp heq)
    simpa only [map_zero] using! hh
  obtain ⟨c, hc⟩ := linear_functional_finite_coordinate_representation
    (schwartzJetCoordinates d N) T.toLinearMap hker
  refine ⟨N, c, fun g => ?_⟩
  simpa only [schwartzJetCoordinates_apply] using! hc g

theorem represented_height_inverse_fourier_jet_representation (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ N : ℕ, ∃ c : JetCoordinateIndex (p + 1) N → ℂ, ∀ g : 𝓢(Ambient (p + 1), ℂ),
      (𝓕⁻ T : 𝓢'(Ambient (p + 1), ℂ)) g =
        ∑ i, c i * iteratedFDeriv ℝ i.1.val g 0
          (fun j => EuclideanSpace.basisFun (Fin (p + 1)) ℝ (i.2 j)) := by
  apply point_supported_distribution_jet_representation
  intro g hc hz
  exact represented_height_inverse_fourier_annihilates_away_zero p w T hT heq g hc hz

end

end RieszRectifiability

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundaryOperatorLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMovingParameterLimit

namespace OAI

/-! Joint convergence through the actual matched gauge and flux coefficients. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedFluxBoundary (n : ℕ) (z : ProfileMatchingBall) (R : ℝ)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralFluxBoundary R (radialMatchedMassFunction n z R)
    (radialMatchedTransportFunction n z R)
    (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R) M)

theorem radialMatchedBoundaryOperator_joint_tendsto
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : innerBoundaryRadius < R) (lam₀ : ℂ)
    (M : ℕ → ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : Tendsto (fun p : ℕ × ℂ => M p.1 p.2) (atTop ×ˢ 𝓝 lam₀) (𝓝 M₀)) :
    Tendsto (fun p : ℕ × ℂ => radialMatchedFluxBoundary (s p.1) (z p.1) R (M p.1 p.2))
      (atTop ×ˢ 𝓝 lam₀)
      (𝓝 (spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
        (radialMatchedFreeTransportFunction z₀ R)
        (spectralGaugeRobin (radialShootingFreeExterior z₀ R)
          (deriv (radialShootingFreeExterior z₀) R) M₀))) := by
  refine spectral_joint_of_moving_parameters
    (fun i lam => radialMatchedFluxBoundary (s i) (z i) R (M i lam)) lam₀ _ ?_
  intro lam hlam
  exact radialMatchedBoundaryOperator_tendsto s hs z z₀ hz hX hm R hR
    (fun i => M i (lam i)) M₀ (hM.comp (tendsto_id.prodMk hlam))

end DefocusingNLS

end OAI

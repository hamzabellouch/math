import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalRobinAnalytic

namespace OAI

/-! The canonical boundary operator in physical gauge. -/

namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonicalFlux_eq_physical (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (Y Z : ℂ → ℝ → E₄) :
    radialMatchedCanonicalFlux n z R Y Z =
      fun t => spectralFluxBoundary R (radialMatchedMassFunction n z R)
        (radialMatchedTransportFunction n z R)
        (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R)
          (radialMatchedCanonicalRobin n z R Y Z t)) := rfl

theorem radialMatchedCanonicalFlux_apply_eq_physical (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (Y Z : ℂ → ℝ → E₄) (t : ℂ) :
    radialMatchedCanonicalFlux n z R Y Z t =
      spectralFluxBoundary R (radialMatchedMassFunction n z R)
        (radialMatchedTransportFunction n z R)
        (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R)
          (radialMatchedCanonicalRobin n z R Y Z t)) := rfl

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousWeight
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileSplice

namespace OAI

/-! The actual matched profile supplies a positive weight for the fixed-harmonic form. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_spectral_weight (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ∃ w : SpectralHarmonicWeight R,
      w.density=(fun r => ‖radialMatchedProfile n z r‖^2) ∧ ∃ c : ℝ, 0 < c ∧
      (∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r) ∧
      (∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) := by
  apply spectralPositiveWeight_exists
  · exact (radialMatchedProfile_differentiable n z hX hz).continuous.norm.pow 2
  · intro r hr
    exact sq_pos_of_pos (norm_pos_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.1))

end DefocusingNLS

end OAI

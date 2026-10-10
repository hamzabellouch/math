import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencilDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightExt

namespace OAI

/-! The actual finite-power pencil derivative, with no limiting coefficient substituted. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance matchedWeakDerivativeNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedWeakOperator_hasDerivAt (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedMassFunction n z)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (lam : ℂ) (hB : HasDerivAt B B' lam) :
    HasDerivAt (fun t => radialMatchedWeakOperator n ell z hX hm R hR t (B t))
      (spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B') lam := by
  have heq := spectralRadialWeightMultiplier_eq_of_density R w
    (spectralContinuousCoefficient R (radialMatchedMassFunction n z)
      (radialMatchedMassFunction_continuous n z hX hm)) hw
  unfold radialMatchedWeakOperator
  rw [← heq]
  exact spectralLowerOrderOperator_hasDerivAt ell R hR _ _ _ B B' lam hB

end DefocusingNLS

end OAI

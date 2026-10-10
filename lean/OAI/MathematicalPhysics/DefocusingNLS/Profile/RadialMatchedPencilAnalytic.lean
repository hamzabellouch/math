import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencil

namespace OAI

/-! Holomorphy of the finite-power matched pencil follows from its actual
mass and transport coefficients and the outgoing Robin family. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance matchedWeakAnalyticNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance matchedPencilAnalyticNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedWeakOperator_analyticAt (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (lam : ℂ) (hB : AnalyticAt ℂ B lam) :
    AnalyticAt ℂ (fun t => radialMatchedWeakOperator n ell z hX hm R hR t (B t)) lam := by
  unfold radialMatchedWeakOperator
  exact spectralLowerOrderOperator_analyticAt ell R hR _ _ _ B lam hB

theorem radialMatchedPencil_analyticAt (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (lam : ℂ) (hB : AnalyticAt ℂ B lam) :
    AnalyticAt ℂ (fun t => s.compactPencil ell hR i
      (radialMatchedWeakOperator n ell z hX hm R hR t (B t))) lam := by
  exact s.compactPencil_analyticAt ell hR i _ lam
    (radialMatchedWeakOperator_analyticAt n ell z hX hm R hR B lam hB)

end DefocusingNLS

end OAI

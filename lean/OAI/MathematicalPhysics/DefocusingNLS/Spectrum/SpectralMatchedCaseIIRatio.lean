import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIModes
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEscapeRatio

namespace OAI

/-! A bounded angular-to-frequency ratio is impossible for an escaping
frequency family of nonzero regular outgoing modes. All radii are constructed. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_bounded_ratio
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C : ℝ) (hC : 0 ≤ C)
    (hratio : ∀ i, ((ell i : ℝ)*(ell i+10))/(1+(lam i).im) ≤ C)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i)) : False := by
  let A := 2*C+25
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let R := innerBoundaryRadius+2*A+2
  have hR : innerBoundaryRadius < R := by dsimp only [R]; linarith
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith [innerBoundaryRadius_bounds.1]
  have hRA : 2*A ≤ R := by dsimp only [R]; linarith [innerBoundaryRadius_bounds.1]
  have hR2 : 2*A ≤ R^2 := by nlinarith
  exact spectralMatched_caseII_modes s hs z z0 hz hX hmatch N hN lam ell hhalf hupper hw
    A R (R+1) hA hR (by linarith) hR2 (spectral_bounded_ratio_caseII ell _ C hC hw hratio) mode

end DefocusingNLS

end OAI

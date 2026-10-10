import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralNormalization

namespace OAI

/-! Case II excludes nonzero radial modes after fixed-ball unit-energy
normalization. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_modes
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R < B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i)) : False := by
  have hB : 0 < B := by linarith [innerBoundaryRadius_bounds.1]
  have hv : ∀ i, ∃ v : RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i),
      (∫ r in (0 : ℝ)..B, spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) v.first v.second r)=1 := by
    intro i
    apply (mode i).normalized (by positivity) _ B hB
    exact (radialMatchedProfile_differentiable (s i) (z i) (hX i) (hmatch i)).continuous.continuousOn
  choose v hv using hv
  exact spectralMatched_caseII_exclusion s hs z z0 hz hX hmatch N hN lam ell hhalf hupper hw
    C R B hC hR hRB hCR hangular (fun i => (v i).first) (fun i => (v i).second)
    (fun i => (v i).first_c2) (fun i => (v i).second_c2) (fun i => (v i).equation)
    (fun i => (v i).bounded) (fun i => (v i).first_top) (fun i => (v i).second_top) hv

end DefocusingNLS

end OAI

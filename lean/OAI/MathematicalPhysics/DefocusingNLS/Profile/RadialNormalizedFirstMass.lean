import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFirstMassLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformGaugeEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformGaugeFirstBoundary

namespace OAI

/-! The physical normalization and its derived Cauchy trace bound imply
weighted L2 vanishing of the first gauge component, uniformly in angular degree. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hmatch

theorem radialMatched_normalized_first_mass_limit (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (lam : ℕ → ℂ) (ell : ℕ → ℕ) (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (F G f g : ℕ → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (F i) (G i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r)) = (F i r,G i r))
    (hnorm : ∀ i, (∫ r in (0 : ℝ)..R,
      spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (F i) (G i) r) ≤ 1)
    (htrace : ∀ᶠ i in atTop, spectralPhysicalShellDensity (F i) (G i) R ≤ M) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      r^11*radialMatchedMassFunction (s i) (z i) r*‖f i r‖^2) atTop (𝓝 0) := by
  obtain ⟨E,_,henergy⟩ := radialMatched_uniform_gauge_energy s hs z z₀ hz hX hmatch
    R hR ell F G f g hF hG hf hg hpair hnorm
  obtain ⟨L,_,hboundary⟩ := radialMatched_uniform_gauge_first_boundary s hs z z₀ hz hX hmatch
    R M hR hM F G f g hf hg hpair htrace
  apply radialMatched_first_mass_limit s hs z z₀ hz hX hmatch R E L hR lam ell hw f g hf hg
    (fun i => ?_) henergy hboundary
  exact radialMatchedGauge_equation (s i) (z i) (hX i) (hmatch i) _ (lam i)
    (F i) (G i) (f i) (g i) (hf i) (hg i) (hpair i) (he i)

end DefocusingNLS

end OAI

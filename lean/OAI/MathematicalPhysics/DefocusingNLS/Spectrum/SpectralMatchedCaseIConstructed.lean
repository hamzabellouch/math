import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseI
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNaturalRadius

namespace OAI

/-! Angular-dominated escape is excluded without any assumed remote
radius or comparison-system data. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseI
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hpos : ∀ i, 0 ≤ (lam i).im)
    (hescape : Tendsto (fun i => ((ell i : ℝ)*(ell i+10))/(1+(lam i).im)) atTop atTop)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hn : ∀ i, ∃ r : ℝ, 0 < r ∧ (f i r ≠ 0 ∨ g i r ≠ 0))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) : False := by
  let E := fun i => spectralNaturalRadius (ell i) (lam i).im
  have hdata : ∀ i, 0 ≤ radialShootingB (profileMatchingParameter (z i)) ∧
      radialShootingB (profileMatchingParameter (z i)) ≤ 1 ∧ 0 ≤ (lam i).im := by
    intro i
    have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
    exact ⟨by linarith [hb.1],by linarith [hb.2],hpos i⟩
  have hE := spectralNaturalRadius_caseI_tendsto ell
    (fun i => radialShootingB (profileMatchingParameter (z i))) (fun i => (lam i).im) hdata hescape
  have hscale : ∀ᶠ i in atTop, (E i)^2 = 256*max ((ell i : ℝ)+1) |(lam i).im| :=
    Eventually.of_forall (fun i => by
      rw [abs_of_nonneg (hpos i)]
      exact (spectralNaturalRadius_data (ell i) (lam i).im).2)
  exact spectralMatched_caseI_exclusion s hs z z0 hz hX hmatch N hN lam ell hhalf hupper
    hpos hescape E hE hscale f g hf hg he hn hbounded hL2f hL2g

end DefocusingNLS

end OAI

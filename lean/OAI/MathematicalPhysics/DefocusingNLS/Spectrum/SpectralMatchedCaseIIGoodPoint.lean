import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIICoercivity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGoodPoint

namespace OAI

/-! Construct bounded initial Cauchy data inside the shell for the actual
normalized Case II modes. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_good_point
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R < B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0))
    (hnorm : ∀ i, (∫ r in R..B, spectralPhysicalShellDensity (f i) (g i) r) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      ∃ r ∈ Icc R ((R+B)/2),
      let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r
      let A := 2*(1+(11/(2*R)+B/4)^2)/((R+B)/2-R)
      ‖q.1.2‖^2+‖q.2.2‖^2 ≤ A ∧
        (Real.sqrt (lam (φ n)).im/48)^2*(‖q.1.1‖^2+‖q.2.1‖^2) ≤ 8*A := by
  obtain ⟨φ,hφ,hc⟩ := spectralMatched_caseII_value_coercivity s hs z z0 hz hX hmatch N hN
    lam ell hhalf hupper hw C R B hC hR hRB.le hCR hangular f g hf hg he hbounded hL2f hL2g
  refine ⟨φ,hφ,?_⟩
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  filter_upwards [hc] with n hn
  simpa only [mul_one] using spectralPhysicalShell_good_point R B 1
    (Real.sqrt (lam (φ n)).im/48) hR0 hRB (by positivity)
    (f (φ n)) (g (φ n)) (hf (φ n)) (hg (φ n)) (hnorm (φ n)) hn

end DefocusingNLS

end OAI

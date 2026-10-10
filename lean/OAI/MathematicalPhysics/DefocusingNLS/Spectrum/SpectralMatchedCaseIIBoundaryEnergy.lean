import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIPositiveBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleEnergyLimit

namespace OAI

/-! The normalized Case II shell gives a uniformly bounded physical Cauchy
trace on a subsequence, with no boundary-data assumption. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_boundary_energy
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
    ∃ (φ : ℕ → ℕ) (M : ℝ), StrictMono φ ∧ 0 ≤ M ∧ ∀ᶠ n in atTop,
      spectralPhysicalShellDensity (f (φ n)) (g (φ n)) B ≤ M := by
  obtain ⟨φ,M,hφ,hM,henergy⟩ := spectralMatched_caseII_oscillatory_bound s hs z z0 hz hX hmatch
    N hN lam ell hhalf hupper hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g hnorm
  obtain ⟨ψ,hψ,hp,hdp⟩ := spectralMatched_caseII_positive_boundary (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN
    (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i))
    (hw.comp hφ.tendsto_atTop) C R B hC hR hRB hCR
    (hφ.tendsto_atTop.eventually hangular) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i)) (fun i => hnorm (φ i))
  have hB : 0 < B := by linarith [innerBoundaryRadius_bounds.1]
  refine ⟨φ ∘ ψ,(3+2*(11/(2*B)+B/4)^2)*(2+M),hφ.comp hψ,by positivity,?_⟩
  apply spectralPhysicalLiouvillePair_eventual_energy_bound B M hB hM
    (fun n => (lam (φ (ψ n))).im) (hw.comp (hφ.comp hψ).tendsto_atTop)
    (f ∘ φ ∘ ψ) (g ∘ φ ∘ ψ) hp hdp
  filter_upwards [hψ.tendsto_atTop.eventually henergy] with n hn
  obtain ⟨a,ha,_,hneg⟩ := hn
  exact hneg B ⟨by linarith [ha.2],le_rfl⟩

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIBoundaryEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformGaugeEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformGaugeBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCrossFluxLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialShellNormalization

namespace OAI

/-! All four Case II boundary limits follow from the single full physical
energy normalization. Gauge energy, boundary pairing and total flux are derived. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_normalized_boundary
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
    (hnorm : ∀ i, (∫ r in (0 : ℝ)..B,
      spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (f i) (g i) r) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (Real.sqrt (lam (φ n)).im : ℂ)*
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.1) atTop (𝓝 0) ∧
      Tendsto (fun n => (Real.sqrt (lam (φ n)).im : ℂ)*
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).2.1) atTop (𝓝 0) ∧
      Tendsto (fun n => (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).1.2) atTop (𝓝 0) ∧
      Tendsto (fun n => (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) B).2.2) atTop (𝓝 0) := by
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hB : 0 < B := hR0.trans hRB
  have hshell i : (∫ r in R..B, spectralPhysicalShellDensity (f i) (g i) r) ≤ 1 :=
    (spectralRadialEnergy_shell_le _ R B (by positivity) hR0.le hRB.le (f i) (g i) (hf i) (hg i)).trans (hnorm i)
  obtain ⟨φ,M,hφ,hM,htrace⟩ := spectralMatched_caseII_boundary_energy s hs z z0 hz hX hmatch
    N hN lam ell hhalf hupper hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g hshell
  have hjet : ∀ i, ∃ f₀ g₀ : ℝ → ℂ, ContDiff ℝ 2 f₀ ∧ ContDiff ℝ 2 g₀ ∧
      ∀ r, (radialMatchedEvenProfile (s (φ i)) (z (φ i)) r*(f₀ r+Complex.I*g₀ r),
        star (radialMatchedEvenProfile (s (φ i)) (z (φ i)) r)*(f₀ r-Complex.I*g₀ r)) = (f (φ i) r,g (φ i) r) := by
    intro i
    obtain ⟨f₀,g₀,hf₀,hg₀,_,_,_,_,_,hp,_⟩ := radialMatchedGaugeJet 2 (by norm_num)
      (s (φ i)) (ell (φ i)) (z (φ i)) (hX (φ i)) (hmatch (φ i)) B hB
      (f (φ i)) (g (φ i)) (hf (φ i)) (hg (φ i))
    exact ⟨f₀,g₀,hf₀,hg₀,hp⟩
  choose f₀ g₀ hf₀ hg₀ hpair using hjet
  obtain ⟨E,_,henergy⟩ := radialMatched_uniform_cross_energy (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B hB (ell ∘ φ) (f ∘ φ) (g ∘ φ) f₀ g₀ (fun i => hf (φ i)) (fun i => hg (φ i))
    hf₀ hg₀ hpair (fun i => hnorm (φ i))
  obtain ⟨L,_,hboundary⟩ := radialMatched_uniform_gauge_boundary (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B M hB hM (f ∘ φ) (g ∘ φ) f₀ g₀ hf₀ hg₀ hpair htrace
  have hflux := radialMatched_sqrt_flux_limit (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B E L hB (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i))
    (hw.comp hφ.tendsto_atTop) (f ∘ φ) (g ∘ φ) f₀ g₀ (fun i => hf (φ i)) (fun i => hg (φ i))
    hf₀ hg₀ (fun i => he (φ i)) hpair henergy hboundary
  obtain ⟨ψ,hψ,hpv,hmv,hpd,hmd⟩ := spectralMatched_caseII_boundary_from_flux
    (s ∘ φ) (hs.comp hφ) (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop)
    (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN (lam ∘ φ) (ell ∘ φ)
    (fun i => hhalf (φ i)) (fun i => hupper (φ i)) (hw.comp hφ.tendsto_atTop)
    C R B hC hR hRB hCR (hφ.tendsto_atTop.eventually hangular) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i))
    (fun i => hshell (φ i)) hflux
  exact ⟨φ ∘ ψ,hφ.comp hψ,hpv,hmv,hpd,hmd⟩

end DefocusingNLS

end OAI

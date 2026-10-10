import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedShellLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForbiddenBoundaryExclusion

namespace OAI

/-! The angular-dominated escaping case is impossible for matched
regular weighted-Sobolev eigenpairs with the constructed comparison and
outgoing data. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseI_exclusion
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hpos : ∀ i, 0 ≤ (lam i).im)
    (hescape : Tendsto (fun i => ((ell i : ℝ)*(ell i+10))/(1+(lam i).im)) atTop atTop)
    (E : ℕ → ℝ) (hE : Tendsto E atTop atTop)
    (hscale : ∀ᶠ i in atTop, (E i)^2 = 256*max ((ell i : ℝ)+1) |(lam i).im|)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hn : ∀ i, ∃ r : ℝ, 0 < r ∧ (f i r ≠ 0 ∨ g i r ≠ 0))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) : False := by
  let b := fun i => radialShootingB (profileMatchingParameter (z i))
  let gamma := fun i => radialShootingA (s i)+(lam i).re-3
  let R := innerBoundaryRadius+1
  have hR : innerBoundaryRadius < R := by dsimp only [R]; linarith
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hdata : ∀ᶠ i in atTop, 0 ≤ b i ∧ b i ≤ 1 ∧ 0 ≤ (lam i).im ∧
      |gamma i| ≤ 8 ∧ 0 < E i ∧ (E i)^2 = 256*max ((ell i : ℝ)+1) (lam i).im := by
    filter_upwards [hscale,hE.eventually (eventually_gt_atTop 0)] with i hi hiE
    have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
    have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    refine ⟨by dsimp only [b]; linarith [hb.1],by dsimp only [b]; linarith [hb.2],hpos i,?_,hiE,?_⟩
    · dsimp only [gamma]
      exact abs_le.mpr ⟨by linarith [hhalf i],by linarith [hupper i]⟩
    · simpa only [abs_of_nonneg (hpos i)] using hi
  obtain ⟨φ,K,J,kap,hφ,hK,hJ,hkap,hcomp⟩ := spectralCaseI_comparisons ell b
    (fun i => (lam i).im) gamma E R hR0 hescape hdata
  have herr := spectralMatched_shell_vanishing (s ∘ φ) (hs.comp hφ) (z ∘ φ) z0
    (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN
    (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i)) (E ∘ φ)
    (hE.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually hscale) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i))
    1 R (by norm_num) hR K J hK hJ kap hkap (1/96) (by norm_num)
  obtain ⟨i,hci,herri,hRE⟩ := (hcomp.and (herr.and
    ((hE.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop R)))).exists
  obtain ⟨hF,Sp,Sm,hVp,hVm,hbp,hbm,hkp,hkm,hextp,hextm,hsp,hsm⟩ := hci
  have hi := herri Sp Sm hVp
    (by simpa only [Complex.ofReal_neg,gamma,b,Function.comp_def] using hVm)
    hbp hbm hkp hkm hextp hextm
  dsimp only at hi
  exact spectralForbidden_boundary_exclusion (radialShootingA (s (φ i))) (b (φ i))
    ((ell (φ i) : ℝ)*(ell (φ i)+10)) (s (φ i)+radialInnerShootingThreshold)
    (radialShootingInner_power_pos (s (φ i)) (profileMatchingParameter (z (φ i))))
    (radialMatchedProfile (s (φ i)) (z (φ i))) (f (φ i)) (g (φ i)) (lam (φ i))
    (radialMatchedProfile_differentiable (s (φ i)) (z (φ i)) (hX (φ i))
      (hmatch (φ i))).continuous.continuousOn (hf (φ i)) (hg (φ i)) (he (φ i)) (hn (φ i))
    R (E (φ i)) K hR0 hRE hF Sp Sm (1/24) (1/96) (by norm_num) (by norm_num)
    (by norm_num) hsp hsm (hi R ⟨le_rfl,hRE⟩).2

end DefocusingNLS

end OAI

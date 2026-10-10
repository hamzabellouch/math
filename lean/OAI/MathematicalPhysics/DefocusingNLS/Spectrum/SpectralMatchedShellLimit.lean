import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedShellAbsorption
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundaryErrorLimit

namespace OAI

/-! Vanishing Green correction for actual eigenpairs along escaping
parameter sequences. The comparison solutions may be selected afterward. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_shell_vanishing
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (E : ℕ → ℝ) (hE : Tendsto E atTop atTop)
    (hscale : ∀ᶠ i in atTop, (E i)^2 = 256*max ((ell i : ℝ)+1) |(lam i).im|)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0))
    (C R : ℝ) (hC : 0 < C) (hR : innerBoundaryRadius < R)
    (K J : ℝ) (hK : 0 ≤ K) (hJ : 0 ≤ J) (kap : ℕ → ℝ)
    (hkap : Tendsto kap atTop atTop) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      ∀ Sp Sm : SpectralScalarBoundarySystem R (E i) K,
      Sp.V = (fun r => (homogeneousSpectralLocalizationFrequency 1
        (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10)) (lam i).im r : ℂ)+
          Complex.I*((radialShootingA (s i)+(lam i).re-3 : ℝ) : ℂ)) →
      Sm.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1)
        (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10)) (lam i).im r : ℂ)+
          Complex.I*((-(radialShootingA (s i)+(lam i).re-3) : ℝ) : ℂ)) →
      Sp.beta = Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1
        (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10)) (lam i).im (E i)) : ℂ) →
      Sm.beta = -Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1)
        (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10)) (lam i).im (E i)) : ℂ) →
      (∀ r ∈ Icc R (E i), kap i ≤ Sp.k r) → (∀ r ∈ Icc R (E i), kap i ≤ Sm.k r) →
      (∀ w : ℂ, ∀ r ∈ Icc R (E i), spectralShellNorm (Sp.k r) (Sp.extension w r) ≤ J*Sp.k R*‖w‖) →
      (∀ w : ℂ, ∀ r ∈ Icc R (E i), spectralShellNorm (Sm.k r) (Sm.extension w r) ≤ J*Sm.k R*‖w‖) →
      let q := spectralPhysicalLiouvillePair (f i) (g i)
      let L := J*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖)
      ∀ r ∈ Icc R (E i),
        spectralShellPairNorm (Sp.k r) (Sm.k r) (q r) ≤ 2*L ∧
        spectralShellPairNorm (Sp.k r) (Sm.k r)
          (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
            eps*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖) := by
  obtain ⟨B,hB,habs⟩ := spectralMatched_shell_absorption s hs z z0 hz hX hmatch N hN lam ell
    hhalf hupper E hE hscale f g hf hg he hbounded hL2f hL2g C R hC hR
  let delta := fun i => (K+1)*(B/E i+C/R)/(kap i)^2
  have hd : Tendsto delta atTop (𝓝 0) := spectralBoundaryError_tendsto E kap hE hkap K B C R
  have hdJ : Tendsto (fun i => (2*J)*delta i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul (2*J)
  intro eps heps
  filter_upwards [habs,hkap.eventually (eventually_gt_atTop 0),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hdJ.eventually (gt_mem_nhds heps),hE.eventually (eventually_ge_atTop R)]
    with i hi hki hsmall hepsi hRE
  intro Sp Sm hVp hVm hbp hbm hkp hkm hextp hextm
  have hi' := hi K J (kap i) hK hJ hki hsmall.le Sp Sm hVp hVm hbp hbm hkp hkm hextp hextm
  dsimp only
  intro r hr
  have ht := hi' r hr
  refine ⟨ht.1,ht.2.trans ?_⟩
  let q := spectralPhysicalLiouvillePair (f i) (g i)
  have hv : 0 ≤ max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖) :=
    (mul_nonneg (Sp.positive_k R ⟨le_rfl,hRE⟩).le (norm_nonneg _)).trans (le_max_left _ _)
  calc
    _ = ((2*J)*delta i)*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖) := by
      dsimp only [delta,q]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hepsi.le hv

end DefocusingNLS

end OAI

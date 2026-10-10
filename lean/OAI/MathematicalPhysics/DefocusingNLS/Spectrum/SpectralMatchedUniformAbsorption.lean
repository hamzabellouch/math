import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedShellBoundary

namespace OAI

/-! Absorption for the matched weighted-Sobolev eigenpair, using its
remote Robin condition and coupled forcing bounds. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_uniform_shell_absorption
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
    (C R₀ : ℝ) (hC : 0 < C) (hR₀ : innerBoundaryRadius < R₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop, ∀ R ∈ Icc R₀ (E i), ∀ K J kap : ℝ,
      0 ≤ K → 0 ≤ J → 0 < kap → (K+1)*(B/E i+C/R)/kap^2 ≤ 1/2 →
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
      (∀ r ∈ Icc R (E i), kap ≤ Sp.k r) → (∀ r ∈ Icc R (E i), kap ≤ Sm.k r) →
      (∀ w : ℂ, ∀ r ∈ Icc R (E i), spectralShellNorm (Sp.k r) (Sp.extension w r) ≤ J*Sp.k R*‖w‖) →
      (∀ w : ℂ, ∀ r ∈ Icc R (E i), spectralShellNorm (Sm.k r) (Sm.extension w r) ≤ J*Sm.k R*‖w‖) →
      let q := spectralPhysicalLiouvillePair (f i) (g i)
      let L := J*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖)
      ∀ r ∈ Icc R (E i),
        spectralShellPairNorm (Sp.k r) (Sm.k r) (q r) ≤ 2*L ∧
        spectralShellPairNorm (Sp.k r) (Sm.k r)
          (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
            2*((K+1)*(B/E i+C/R)/kap^2)*L := by
  obtain ⟨B,hB,hremote⟩ := spectralRemote_matched_endpoint s hs z z0 hz hX hmatch N hN lam ell
    hhalf hupper E hE hscale f g hf hg he hbounded hL2f hL2g
  refine ⟨B,hB,?_⟩
  filter_upwards [hremote,hs.tendsto_atTop.eventually (radialMatched_shell_boundary_absorb C hC)] with i hrem habs
  intro R hRR K J kap hK hJ hkap hsmall Sp Sm hVp hVm hbp hbm hkp hkm hextp hextm
  have hR : innerBoundaryRadius < R := hR₀.trans_le hRR.1
  have hRE : R ≤ E i := hRR.2
  let q := spectralPhysicalLiouvillePair (f i) (g i)
  let L := J*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖)
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hqc : ContinuousOn q (Icc R (E i)) :=
    (spectralPhysicalLiouvillePair_continuousOn (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10))
      (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i)) (lam i)
      (f i) (g i) (hf i) (hg i) (he i)).mono (fun r hr => hR0.trans_le hr.1)
  apply habs (z i) (hX i) (hmatch i) R (E i) K kap B L hR hRE hkap hK hB hsmall
    Sp Sm hkp hkm q hqc
  · intro r hr
    rw [hVp]
    exact (spectralPhysicalLiouvillePair_equation (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10))
      (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i)) (lam i)
      (f i) (g i) (hf i) (hg i) (he i) r (hR0.trans_le hr.1)).1
  · intro r hr
    rw [hVm]
    exact (spectralPhysicalLiouvillePair_equation (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) ((ell i : ℝ)*(ell i+10))
      (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i)) (lam i)
      (f i) (g i) (hf i) (hg i) (he i) r (hR0.trans_le hr.1)).2
  · rw [hbp,hbm]
    exact hrem
  · intro r hr
    apply max_le
    · exact (hextp (q R).1.1 r hr).trans (by
        dsimp only [L]
        calc
          _ = J*(Sp.k R*‖(q R).1.1‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hJ)
    · exact (hextm (q R).2.1 r hr).trans (by
        dsimp only [L]
        calc
          _ = J*(Sm.k R*‖(q R).2.1‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hJ)

end DefocusingNLS

end OAI

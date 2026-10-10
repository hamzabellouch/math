import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNaturalRadius
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedShellLimit

namespace OAI

/-! The actual mixed Case II eigenpair has uniformly vanishing shell
correction and a no-turn comparison with the precise outgoing slope. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_shell
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) :
    let b := fun i => radialShootingB (profileMatchingParameter (z i))
    let gamma := fun i => radialShootingA (s i)+(lam i).re-3
    let E := fun i => spectralNaturalRadius (ell i) (lam i).im
    let dp := fun i => spectralTurningRootScale ((ell i : ℝ)*(ell i+10))
      (spectralTurningRoot 1 (b i) ((ell i : ℝ)*(ell i+10)) (lam i).im)
    ∃ (φ : ℕ → ℕ) (K J : ℝ) (kap eps : ℕ → ℝ),
      StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ Tendsto kap atTop atTop ∧
      (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop,
      ∃ Sp Sm : SpectralScalarBoundarySystem R (E (φ n)) K,
        SpectralTurningComparison Sp J 1 (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (lam (φ n)).im (gamma (φ n)) (dp (φ n)) ∧
        SpectralNoTurnComparison Sm J (eps n) (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (lam (φ n)).im (-gamma (φ n)) ∧
        let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n))
        ∀ r ∈ Icc R (E (φ n)),
          spectralShellPairNorm (Sp.k r) (Sm.k r) (q r) ≤
            2*(J*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖)) ∧
          spectralShellPairNorm (Sp.k r) (Sm.k r)
            (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
              delta*max (Sp.k R*‖(q R).1.1‖) (Sm.k R*‖(q R).2.1‖) := by
  dsimp only
  let b := fun i => radialShootingB (profileMatchingParameter (z i))
  let gamma := fun i => radialShootingA (s i)+(lam i).re-3
  let E := fun i => spectralNaturalRadius (ell i) (lam i).im
  have hE : Tendsto E atTop atTop := spectralNaturalRadius_frequency_tendsto ell _ hw
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hscale : ∀ᶠ i in atTop, (E i)^2 = 256*max ((ell i : ℝ)+1) |(lam i).im| := by
    filter_upwards [hw.eventually (eventually_ge_atTop 0)] with i hi
    rw [abs_of_nonneg hi]
    exact (spectralNaturalRadius_data (ell i) (lam i).im).2
  have hdata : ∀ᶠ i in atTop, 0 ≤ b i ∧ b i ≤ 1 ∧ |gamma i| ≤ 8 ∧ 0 < E i ∧
      (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im ∧
      (E i)^2 = 256*max ((ell i : ℝ)+1) (lam i).im := by
    filter_upwards [hangular] with i hi
    have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
    have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    refine ⟨by dsimp only [b]; linarith [hb.1],by dsimp only [b]; linarith [hb.2],?_,
      (spectralNaturalRadius_data (ell i) (lam i).im).1,hi,(spectralNaturalRadius_data (ell i) (lam i).im).2⟩
    dsimp only [gamma]
    exact abs_le.mpr ⟨by linarith [hhalf i],by linarith [hupper i]⟩
  obtain ⟨φ,K,J,kap,eps,hφ,hK,hJ,hkap,heps,heps0,hcomp⟩ :=
    spectralCaseII_comparisons ell b (fun i => (lam i).im) gamma E C R hC hR0 hCR hw hdata
  refine ⟨φ,K,J,kap,eps,hφ,hK,hJ,hkap,heps,heps0,?_⟩
  intro delta hdelta
  have herr := spectralMatched_shell_vanishing (s ∘ φ) (hs.comp hφ) (z ∘ φ) z0
    (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i)) N hN
    (lam ∘ φ) (ell ∘ φ) (fun i => hhalf (φ i)) (fun i => hupper (φ i)) (E ∘ φ)
    (hE.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually hscale) (f ∘ φ) (g ∘ φ)
    (fun i => hf (φ i)) (fun i => hg (φ i)) (fun i => he (φ i))
    (fun i => hbounded (φ i)) (fun i => hL2f (φ i)) (fun i => hL2g (φ i))
    1 R (by norm_num) hR K J hK hJ kap hkap delta hdelta
  filter_upwards [hcomp,herr] with i hci hei
  obtain ⟨Sp,Sm,hsp,hsm,hkp,hkm⟩ := hci
  refine ⟨Sp,Sm,hsp,hsm,?_⟩
  apply hei Sp Sm hsp.2.1
    (by simpa only [Complex.ofReal_neg,gamma,b,Function.comp_def] using hsm.2.1)
  · simpa only [Complex.ofReal_one,one_mul,b,Function.comp_def] using hsp.2.2.1
  · exact hsm.2.2.1
  · exact hkp
  · exact hkm
  · exact hsp.2.2.2.1
  · exact hsm.2.2.2.1

end DefocusingNLS

end OAI

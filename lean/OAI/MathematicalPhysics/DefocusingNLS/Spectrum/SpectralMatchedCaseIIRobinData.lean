import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIUniformShell
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIUniformWeights
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinNormBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellInnerRobin

namespace OAI

/-! Local inward Robin data for the actual mixed high-frequency eigenpair. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_robin_data
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) :
    ∃ (φ : ℕ → ℕ) (A : ℝ), StrictMono φ ∧ 0 ≤ A ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, ∀ r ∈ Icc R B,
        ∃ alpha : ℂ, alpha.re ≤ -Real.sqrt (lam (φ n)).im/48 ∧
          ‖alpha‖ ≤ A*Real.sqrt (lam (φ n)).im ∧
          let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r
          ‖q.1.2-alpha*q.1.1‖ ≤ delta*(C/R^2+11)*Real.sqrt (lam (φ n)).im*
            (‖q.1.1‖+‖q.2.1‖) := by
  let b := fun i => radialShootingB (profileMatchingParameter (z i))
  let gamma := fun i => radialShootingA (s i)+(lam i).re-3
  let E := fun i => spectralNaturalRadius (ell i) (lam i).im
  have hE : Tendsto E atTop atTop := spectralNaturalRadius_frequency_tendsto ell _ hw
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
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
  obtain ⟨hrp,hdp,hdpp,hp⟩ := spectralTurningRoot_caseII_data ell b (fun i => (lam i).im) gamma E hw (by
    filter_upwards [hdata,hw.eventually (eventually_ge_atTop 0)] with i hi hwi
    exact ⟨hi.1,hi.2.1,hwi,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.2⟩)
  have hweights := spectralCaseII_uniform_weights ell b (fun i => (lam i).im) gamma _ _ E C R B
    hC hR0 hRB hCR hw hrp hp hangular
  obtain ⟨φ,K,J,kap,eps,hφ,hK,hJ,hkap,heps,heps0,hshell⟩ :=
    spectralMatched_caseII_uniform_shell s hs z z0 hz hX hmatch N hN lam ell hhalf hupper
      hw C R B hC hR hRB hCR hangular f g hf hg he hbounded hL2f hL2g
  let D := C/R^2+11
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨φ,J*D,hφ,mul_nonneg hJ hD.le,?_⟩
  intro delta hdelta
  filter_upwards [hshell delta hdelta,hφ.tendsto_atTop.eventually hweights,
    (hE.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop B)] with n hsn hwn hBE
  intro r hr
  obtain ⟨Sp,Sm,hsp,hsm,herr⟩ := hsn r hr
  have hws := hwn r hr
  have hEr : r ≤ E (φ n) := hr.2.trans hBE
  have hkp' : (Sp.k r)^2 ≤ D*Real.sqrt (lam (φ n)).im := by
    rw [hsp.1]
    exact hws.1.2
  have hkm' : (Sm.k r)^2 ≤ D*Real.sqrt (lam (φ n)).im := by
    rw [hsm.1]
    exact hws.2.2
  refine ⟨(Sp.U r).2/(Sp.U r).1,?_,?_,?_⟩
  · have hslope := hsp.2.2.2.2.1
    have hlo : Real.sqrt (lam (φ n)).im/2 ≤ (Sp.k r)^2 := by rw [hsp.1]; exact hws.1.1
    linarith
  · exact (Sp.inner_slope_norm hEr J hsp.2.2.2.1).trans (by
      calc J*(Sp.k r)^2 ≤ J*(D*Real.sqrt (lam (φ n)).im) := mul_le_mul_of_nonneg_left hkp' hJ
           _ = _ := by ring)
  · have he := (spectralCoupled_inner_robin_scaled Sp Sm hEr
        (spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r) delta
        (D*Real.sqrt (lam (φ n)).im) hdelta.le hkp' hkm' (herr r ⟨le_rfl,hEr⟩).2).1
    convert he using 1
    ring

end DefocusingNLS

end OAI

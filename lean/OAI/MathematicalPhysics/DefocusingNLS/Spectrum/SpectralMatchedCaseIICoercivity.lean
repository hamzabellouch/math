import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIUniformShell
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIUniformWeights
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIRobinCoercivity

namespace OAI

/-! The actual mixed high-frequency eigenpair has local value control by
its first derivative everywhere on a fixed shell. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_value_coercivity
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
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop, ∀ r ∈ Icc R B,
      let q := spectralPhysicalLiouvillePair (f (φ n)) (g (φ n)) r
      (Real.sqrt (lam (φ n)).im/48)*(‖q.1.1‖+‖q.2.1‖) ≤ 2*(‖q.1.2‖+‖q.2.2‖) := by
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
  let delta := (192*D)⁻¹
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hsmall : 48*D*delta ≤ 1/4 := by
    dsimp only [delta]
    field_simp
    nlinarith
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hshell delta hdelta,hφ.tendsto_atTop.eventually hweights,
    hφ.tendsto_atTop.eventually hdata,heps0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    (hw.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (2*(B^2/16+1))),
    (hE.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop B)] with n hsn hwn hdn hen hlarge hBE
  intro r hr
  obtain ⟨Sp,Sm,hsp,hsm,herr⟩ := hsn r hr
  have hws := hwn r hr
  have hwp : 0 < (lam (φ n)).im := by
    dsimp only [Function.comp_def] at hlarge
    nlinarith [sq_nonneg B]
  have hnu := Real.sqrt_pos.mpr hwp
  have hFs := spectralCaseII_shell_frequency (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
    (lam (φ n)).im C R B r hdn.1 hdn.2.1 (by positivity) hC hR0 hr.1 hr.2 hlarge hdn.2.2.2.2.1 hCR
  have hFp : (Real.sqrt (lam (φ n)).im)^2/2 ≤
      homogeneousSpectralLocalizationFrequency (-1) (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10)) (lam (φ n)).im r := by
    rw [Real.sq_sqrt hwp.le]
    exact hFs.2.1
  have hEr : r ≤ E (φ n) := hr.2.trans hBE
  have hkp : Real.sqrt (lam (φ n)).im/2 ≤ (Sp.k r)^2 := by
    rw [hsp.1]
    exact hws.1.1
  have hkp' : (Sp.k r)^2 ≤ D*Real.sqrt (lam (φ n)).im := by
    rw [hsp.1]
    exact hws.1.2
  have hkm' : (Sm.k r)^2 ≤ D*Real.sqrt (lam (φ n)).im := by
    rw [hsm.1]
    exact hws.2.2
  exact spectralCaseII_robin_coercivity Sp Sm hEr J _ _ _ _ _ (eps n) _ D delta
    hsp hsm hnu hD.le hdelta.le hen.le hsmall hkp hkp' hkm' hFp _ (herr r ⟨le_rfl,hEr⟩).2

end DefocusingNLS

end OAI

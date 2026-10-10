import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteNaturalRadius

namespace OAI

/-! At the natural remote radius the actual matched eigenpair has the
outgoing boundary error needed by the coupled Green argument. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_endpoint
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
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ i in atTop,
      let q := spectralPhysicalLiouvillePair (f i) (g i) (E i)
      let b := radialShootingB (profileMatchingParameter (z i))
      let eta := (ell i : ℝ)*(ell i+10)
      max ‖q.1.2-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 b eta (lam i).im (E i)) : ℂ)*q.1.1‖
        ‖q.2.2-(-Complex.I)*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta (lam i).im (E i)) : ℂ)*q.2.1‖ ≤
        A/E i*max ‖q.1.1‖ ‖q.2.1‖ := by
  let L := fun i => Real.log (E i/2)
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (hE.atTop_div_const (by norm_num))
  have hEp : ∀ᶠ i in atTop, 0 < E i := hE.eventually (eventually_gt_atTop 0)
  have hsmall := hEp.and hscale
  have hb : ∀ᶠ i in atTop,
      |(lam i).im| *Real.exp (-2*L i) ≤ 1/64 ∧
      |(ell i : ℝ)*(ell i+10)| *Real.exp (-4*L i) ≤ 1/256 := by
    filter_upwards [hsmall] with i hi
    exact spectralRemote_natural_radius_bounds (ell i) (lam i).im (E i) hi.1 hi.2
  obtain ⟨A,hA,hbound⟩ := spectralRemote_matched_robin s hs z z0 hz hX hmatch N hN lam
    (fun i => (ell i : ℝ)*(ell i+10)) hhalf hupper L hL
    (hb.mono (fun _ hi => hi.1)) (hb.mono (fun _ hi => hi.2))
    f g hf hg he hbounded hL2f hL2g
  refine ⟨A,hA,?_⟩
  filter_upwards [hEp,hbound] with i hi hbi
  have ht : Real.log (E i) ∈ Ioi (L i) :=
    Real.log_lt_log (by positivity) (by linarith)
  have hr := hbi (Real.log (E i)) ht
  rw [← spectralPhysicalLiouvillePair_remote, Real.exp_log hi] at hr
  dsimp only at hr
  rw [homogeneousDiagonal_apply] at hr
  exact hr

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIINormalizedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialNormalizedFirstMass
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationEnergyLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVanishingEnergy

namespace OAI

/-! Case II is impossible: the outgoing boundary limits, pressure-free test,
and dilation identity force a physically normalized mode to have zero energy. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_caseII_exclusion
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hw : Tendsto (fun i => (lam i).im) atTop atTop)
    (C R B : ℝ) (hC : 0 ≤ C) (hR : innerBoundaryRadius < R) (hRB : R < B) (hCR : 2*C ≤ R^2)
    (hangular : ∀ᶠ i in atTop, (ell i : ℝ)*(ell i+10)+99/4 ≤ C*(lam i).im)
    (F G : ℕ → ℝ → ℂ) (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i) (F i) (G i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(F i r,G i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (F i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (G i) r‖^2) (Ioi 0))
    (hnorm : ∀ i, (∫ r in (0 : ℝ)..B,
      spectralRadialEnergyDensity ((ell i : ℝ)*(ell i+10)) (F i) (G i) r)=1) : False := by
  have hB : 0 < B := by linarith [innerBoundaryRadius_bounds.1]
  obtain ⟨φ,hφ,hpv,hmv,hpd,hmd⟩ := spectralMatched_caseII_normalized_boundary s hs z z0 hz hX hmatch
    N hN lam ell hhalf hupper hw C R B hC hR hRB hCR hangular F G hF hG he hbounded hL2f hL2g
    (fun i => (hnorm i).le)
  have hphys := spectralPhysicalLiouvillePair_weighted_energy_limit B hB (fun i => (lam (φ i)).im)
    (hw.comp hφ.tendsto_atTop) (F ∘ φ) (G ∘ φ) hpv hmv hpd hmd
  have hjet : ∀ i, ∃ f g : ℝ → ℂ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      ∀ r, (radialMatchedEvenProfile (s (φ i)) (z (φ i)) r*(f r+Complex.I*g r),
        star (radialMatchedEvenProfile (s (φ i)) (z (φ i)) r)*(f r-Complex.I*g r))=(F (φ i) r,G (φ i) r) := by
    intro i
    obtain ⟨f,g,hf,hg,_,_,_,_,_,hp,_⟩ := radialMatchedGaugeJet 2 (by norm_num)
      (s (φ i)) (ell (φ i)) (z (φ i)) (hX (φ i)) (hmatch (φ i)) B hB
      (F (φ i)) (G (φ i)) (hF (φ i)) (hG (φ i))
    exact ⟨f,g,hf,hg,hp⟩
  choose f g hf hg hp using hjet
  have hbe := radialMatched_weighted_gauge_boundary_limit (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B hB (fun i => (lam (φ i)).im) (hw.comp hφ.tendsto_atTop) (F ∘ φ) (G ∘ φ) f g hf hg hp hphys
  have htrace : ∀ᶠ i in atTop, spectralPhysicalShellDensity (F (φ i)) (G (φ i)) B ≤ 1 := by
    filter_upwards [(hw.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop 1),
      hphys.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with i hi hei
    have hp0 : 0 ≤ B^11*((lam (φ i)).im-1)*(‖F (φ i) B‖^2+‖G (φ i) B‖^2) := by positivity
    dsimp only [Function.comp_def,spectralWeightedCauchyEnergy,spectralPhysicalShellDensity] at hei ⊢
    nlinarith only [hp0,hei]
  have hfirst := radialMatched_normalized_first_mass_limit (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B 1 hB (by norm_num) (lam ∘ φ) (ell ∘ φ) (hw.comp hφ.tendsto_atTop)
    (F ∘ φ) (G ∘ φ) f g (fun i => hF (φ i)) (fun i => hG (φ i)) hf hg
    (fun i => he (φ i)) hp (fun i => (hnorm (φ i)).le) htrace
  obtain ⟨M,hM,hfull⟩ := radialMatched_uniform_gauge_energy (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B hB (ell ∘ φ) (F ∘ φ) (G ∘ φ) f g (fun i => hF (φ i)) (fun i => hG (φ i)) hf hg hp
    (fun i => (hnorm (φ i)).le)
  have hEq i := radialMatchedGauge_equation (s (φ i)) (z (φ i)) (hX (φ i)) (hmatch (φ i))
    (((ell (φ i) : ℝ)*(ell (φ i)+10) : ℝ) : ℂ) (lam (φ i)) (F (φ i)) (G (φ i))
    (f i) (g i) (hf i) (hg i) (hp i) (he (φ i))
  have hangular' : ∀ᶠ i in atTop, (ell (φ i) : ℝ)*(ell (φ i)+10) ≤ C*(lam (φ i)).im :=
    (hφ.tendsto_atTop.eventually hangular).mono (fun i hi => by linarith)
  have hgrad := radialMatched_dilation_energy_limit (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B M C (hR.trans hRB) hM hC (lam ∘ φ) (fun i => (ell (φ i) : ℝ)*(ell (φ i)+10))
    (fun _ => by positivity) (fun i => hhalf (φ i)) (fun i => hupper (φ i)) (hw.comp hφ.tendsto_atTop)
    hangular' f g hf hg hEq hfull hfirst hbe
  have hzero := radialMatched_gradient_to_energy_limit (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B hB (fun i => (lam (φ i)).im) (fun i => (ell (φ i) : ℝ)*(ell (φ i)+10))
    (hw.comp hφ.tendsto_atTop) (fun _ => by positivity) f g
    (fun i => (hf i).of_le (by norm_num)) (fun i => (hg i).of_le (by norm_num)) hgrad hfirst hbe
  have hzphys := radialMatched_vanishing_physical_energy (s ∘ φ) (hs.comp hφ)
    (z ∘ φ) z0 (hz.comp hφ.tendsto_atTop) (fun i => hX (φ i)) (fun i => hmatch (φ i))
    B hB (fun i => (ell (φ i) : ℝ)*(ell (φ i)+10)) (fun _ => by positivity)
    (F ∘ φ) (G ∘ φ) f g (fun i => hF (φ i)) (fun i => hG (φ i)) hf hg hp hzero
  have hbad : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,hnorm] using hzphys
  have h10 : (1 : ℝ)=0 := tendsto_nhds_unique tendsto_const_nhds hbad
  norm_num at h10

end DefocusingNLS

end OAI

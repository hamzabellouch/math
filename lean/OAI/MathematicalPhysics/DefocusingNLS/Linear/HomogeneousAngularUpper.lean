import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGaugeAngular

namespace OAI

/-! # Actual bounded finite-energy radial eigenmodes have real part below four -/

open Set Filter Topology Asymptotics MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem homogeneous_matched_angular_upper :
    ∀ᶠ n : ℕ in atTop, ∀ z : ProfileMatchingBall,
    HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
    radialMatchingMap n z = 0 → ∀ eta : ℝ, 0 ≤ eta → ∀ N : ℕ, 7 ≤ N →
    ∀ lam : ℂ, 4 ≤ lam.re → ∀ F G : ℝ → ℂ,
    ContDiff ℝ 2 F → ContDiff ℝ 2 G →
    IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) (eta : ℂ) lam F G →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(F r, G r)‖ ≤ M) →
    IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N F r‖ ^ 2) (Ioi 0) →
    IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N G r‖ ^ 2) (Ioi 0) →
    ∀ r, 0 ≤ r → F r = 0 ∧ G r = 0 := by
  filter_upwards [radialMatched_angular_upper_exclusion] with n hn z hX hz eta heta N hN
    lam hlam F G hF hG he hbounded hL2F hL2G
  let ν := radialShootingNu (n + radialInnerShootingThreshold) z
  have hm : 1 ≤ n + radialInnerShootingThreshold := by
    have := radialShootingInner_power_pos n (profileMatchingParameter z)
    omega
  obtain ⟨Yp, hYp⟩ := canonical_holomorphic_circular_allOrders ν ν (star ν) (eta : ℂ)
    (radialShootingM z) (n + radialInnerShootingThreshold) hm (Real.log innerBoundaryRadius)
    hX (radialShootingM_ne_zero z) (1, 0)
  obtain ⟨Ym, hYm⟩ := canonical_holomorphic_circular_allOrders ν ν (star ν) (eta : ℂ)
    (radialShootingM z) (n + radialInnerShootingThreshold) hm (Real.log innerBoundaryRadius)
    hX (radialShootingM_ne_zero z) (0, 1)
  obtain ⟨f, g, hf, hg, u, _, _, _, _, hpair, _⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n 0 z hX hz 1 (by norm_num) F G hF hG
  have hdec := homogeneous_matched_gauge_decay n z hX hz (eta : ℂ) N hN lam hlam
    F G hF hG he hbounded hL2F hL2G Yp Ym hYp hYm f g hf hg hpair
  have heq := homogeneousGauge_angular_system n z hX hz eta lam f g hf hg
    (radialMatchedGauge_equation n z hX hz (eta : ℂ) lam F G f g hf hg hpair he)
  have hc : ∀ j, ContDiff ℝ 2 (homogeneousGaugeRealChannels f g j) := by
    intro j
    fin_cases j
    · exact Complex.reCLM.contDiff.comp hf
    · exact Complex.imCLM.contDiff.comp hf
    · exact Complex.reCLM.contDiff.comp hg
    · exact Complex.imCLM.contDiff.comp hg
  have hd : ∀ j, HasRadialEnergyDecay (homogeneousGaugeRealChannels f g j) := by
    intro j
    fin_cases j
    · exact hdec.1 Complex.reCLM
    · exact hdec.1 Complex.imCLM
    · exact hdec.2 Complex.reCLM
    · exact hdec.2 Complex.imCLM
  have hzall := hn z hX hz eta lam.re lam.im heta hlam (homogeneousGaugeRealChannels f g) hc hd heq
  intro r hr
  have hfr : (f r).re = 0 := hzall 0 r hr
  have hfi : (f r).im = 0 := hzall 1 r hr
  have hgr : (g r).re = 0 := hzall 2 r hr
  have hgi : (g r).im = 0 := hzall 3 r hr
  have hf0 : f r = 0 := Complex.ext (by simpa using hfr) (by simpa using hfi)
  have hg0 : g r = 0 := Complex.ext (by simpa using hgr) (by simpa using hgi)
  have hp := hpair r
  rw [hf0, hg0] at hp
  simpa only [mul_zero, add_zero, sub_zero, Prod.mk.injEq, eq_comm] using hp

end DefocusingNLS

end OAI

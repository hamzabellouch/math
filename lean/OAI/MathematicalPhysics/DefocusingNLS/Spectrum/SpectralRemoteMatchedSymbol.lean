import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteOutgoingSymbol

namespace OAI

/-! The weighted-Sobolev outgoing selection theorem supplies the individual
symbol hypothesis for actual matched-profile eigenpairs. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_eigenpair_symbol
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) eta lam f g)
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f r,g r)‖ ≤ M)
    (hL2f : IntegrableOn (fun r => r^11*‖iteratedDeriv N f r‖^2) (Ioi 0))
    (hL2g : IntegrableOn (fun r => r^11*‖iteratedDeriv N g r‖^2) (Ioi 0))
    (Yp Ym : ℂ → ℝ → SpectralRemoteSpace)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Ym) :
    HasLogJetBound 1 (spectralRemoteEigenpairState f g) := by
  let m := n+radialInnerShootingThreshold
  let nu := radialShootingNu m z
  let nuPlus := nu-2*lam
  let nuMinus := star nu-2*lam
  have hp := homogeneous_canonical_circular_value_logJets nu nuPlus nuMinus eta (radialShootingM z)
    m (Real.log innerBoundaryRadius) hX (Yp lam) (1,0) (hYp.1 lam) (hYp.2.1 lam) (hYp.2.2.2 lam)
  have hm := homogeneous_canonical_circular_value_logJets nu nuPlus nuMinus eta (radialShootingM z)
    m (Real.log innerBoundaryRadius) hX (Ym lam) (0,1) (hYm.1 lam) (hYm.2.1 lam) (hYm.2.2.2 lam)
  have hnu : nu.re = -2*radialShootingA n := by
    have hn := radialShootingNu_physical n z
    change nu = _ at hn
    rw [hn]
    simp [Complex.mul_re,Complex.mul_im]
  have ha : 0 ≤ radialShootingA n := by unfold radialShootingA; positivity
  have hsp : nuPlus.re ≤ 1 := by
    dsimp only [nuPlus]
    norm_num [Complex.sub_re,Complex.mul_re,hnu]
    linarith
  have hsm : nuMinus.re ≤ 1 := by
    dsimp only [nuMinus]
    norm_num [Complex.sub_re,Complex.mul_re,Complex.star_def,hnu]
    linarith
  obtain ⟨a,R,hR,htail⟩ := homogeneous_matched_pair_canonical_tail n z hX hz eta N hN lam hhalf
    f g hf hg he hbounded hL2f hL2g Yp Ym hYp hYm
  exact spectralRemote_outgoing_span_symbol nuPlus nuMinus 1 f g hf hg (Yp lam) (Ym lam) a
    hp.1 hp.2 hm.1 hm.2 hsp hsm ((eventually_ge_atTop R).mono (fun r hr => htail r hr))

end DefocusingNLS

end OAI

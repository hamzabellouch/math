import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedBounded
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEigenpairOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteUniformRobin

namespace OAI

/-! Actual matched weighted-Sobolev eigenpairs satisfy the uniform remote
Liouville Robin estimate. Every outgoing and coefficient-symbol input is
derived from the profile and eigenpair equations. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_robin
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i) = 0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (eta : ℕ → ℝ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (homega : ∀ᶠ i in atTop, |(lam i).im| *Real.exp (-2*L i) ≤ 1/64)
    (heta : ∀ᶠ i in atTop, |eta i| *Real.exp (-4*L i) ≤ 1/256)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (he : ∀ i, IsHarmonicRadialEigenpair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) (eta i : ℂ) (lam i) (f i) (g i))
    (hbounded : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f i r,g i r)‖ ≤ M)
    (hL2f : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (f i) r‖^2) (Ioi 0))
    (hL2g : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (g i) r‖^2) (Ioi 0)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ i in atTop, ∀ t ∈ Ioi (L i),
      let q := spectralRemoteLiouvilleState (Real.exp t) (spectralRemoteEigenpairState (f i) (g i) t)
      ‖spectralPhysicalDerivativeMap q-homogeneousDiagonal
        (Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1
          (radialShootingB (profileMatchingParameter (z i))) (eta i) (lam i).im (Real.exp t)) : ℂ))
        (-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1)
          (radialShootingB (profileMatchingParameter (z i))) (eta i) (lam i).im (Real.exp t)) : ℂ))
        (spectralPhysicalValueMap q)‖ ≤ A/Real.exp t*‖spectralPhysicalValueMap q‖ := by
  let b := fun i => radialShootingB (profileMatchingParameter (z i))
  let c := spectralRemoteLeadingCoefficient (fun i => (lam i).im) eta
  let B := fun i t => spectralRemotePhysicalBounded (radialShootingA (s i)) (b i) (lam i).re
    (spectralDiagonalCoefficient (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i) (Real.exp t)))
    (spectralCrossCoefficient (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i) (Real.exp t)))
  let Y := fun i => spectralRemoteEigenpairState (f i) (g i)
  have hc : HasUniformLogJetBound L 0 c := spectralRemote_leading_coefficient_symbol homega heta
  have hB : HasUniformLogJetBound L 0 B :=
    spectralRemote_matched_uniform_bounded s hs z z0 hz L hL (fun i => (lam i).re) hhalf hupper
  have hci : ∀ᶠ i in atTop, HasLogJetBound 0 (c i) :=
    Eventually.of_forall (fun i => spectralRemote_leading_individual _ _ i)
  have hBi : ∀ᶠ i in atTop, HasLogJetBound 0 (B i) :=
    Eventually.of_forall (fun i => spectralRemote_matched_bounded_symbol (s i) (z i) (hX i) (lam i).re)
  have hYi : ∀ᶠ i in atTop, HasLogJetBound 1 (Y i) :=
    Eventually.of_forall (fun i => spectralRemote_matched_state_symbol (s i) (z i) (hX i) (hmatch i)
      (eta i) N hN (lam i) (hhalf i) (f i) (g i) (hf i) (hg i) (he i)
      (hbounded i) (hL2f i) (hL2g i))
  have hb : ∀ᶠ i in atTop, 0 ≤ b i ∧ b i ≤ 1 := by
    apply Eventually.of_forall
    intro i
    have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
    constructor <;> dsimp only [b] <;> linarith [hb.1,hb.2]
  have hode : ∀ᶠ i in atTop, ∀ t ∈ Ioi (L i),
      HasDerivAt (Y i) (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c i t)+B i t) (Y i t)) t := by
    apply Eventually.of_forall
    intro i t ht
    have hcEq : spectralRemoteLeadingCoefficient (fun _ => (lam i).im) (fun _ => eta i) 0 t = c i t := by
      funext j
      rfl
    have hd := spectralRemoteEigenpairState_operator (radialShootingA (s i)) (b i) (eta i)
      (s i+radialInnerShootingThreshold) (radialMatchedProfile (s i) (z i))
      (f i) (g i) (lam i) (hf i) (hg i) (he i) t
    rw [hcEq] at hd
    exact hd

  exact spectralRemote_uniform_robin hL 1 b eta (fun i => (lam i).im) c B Y hc hB hci hBi hYi
    (spectralRemote_leading_coefficient_small homega heta)
    (fun i t => spectralRemote_leading_endpoint _ _ i t) hb hode

end DefocusingNLS

end OAI

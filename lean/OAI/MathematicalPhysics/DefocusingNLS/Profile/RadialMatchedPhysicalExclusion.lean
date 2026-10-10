import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalPencil
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPencilExclusion

namespace OAI

/-! The checked singular pencil limit excludes actual classical eigenmodes,
with the physical outgoing Robin condition and actual profile coefficients. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedPhysical_eventually_zero
    (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z₀)<R)
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (hmass : F.limitWeight.density=radialMatchedFreeMassFunction z₀)
    (hw : ∀ i, (F.weight i).density=radialMatchedMassFunction (s i) (z i))
    (hp : ∀ i, F.pressure i=fun r =>
      ‖radialMatchedProfile (s i) (z i) r‖^(2*(s i+radialInnerShootingThreshold)))
    (ha : ∀ i, F.scale i=radialShootingA (s i))
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hζ₀ : -(1/32 : ℝ)≤ζ₀.re)
    (M : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto (fun i => spectralFluxBoundary R (radialMatchedMassFunction (s i) (z i) R)
      (radialMatchedTransportFunction (s i) (z i) R)
      (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
        (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop (𝓝 B₀))
    (hBoundary : B₀=spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
      (radialMatchedFreeTransportFunction z₀ R)
      (spectralGaugeRobin (radialShootingFreeExterior z₀ R) (deriv (radialShootingFreeExterior z₀) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R))))
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)) ≠ 0)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) ζ₀ ≠ 0) :
    ∀ᶠ i in atTop, ∀ f g : ℝ → ℂ, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      IsHarmonicRadialEigenpair (radialShootingA (s i))
        (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i)) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) (ζ i) f g →
      (deriv f R,deriv g R)=M i (f R,g R) →
      ∀ r ∈ Ioc 0 R, f r=0 ∧ g r=0 := by
  let hR := (radialMatchedCore_radius_pos z₀).trans hLR
  have hk := radialMatchedPencil_eventually_kernel_zero ell s hs z z₀ hz hX hm
    hz₁ hz₀ R hLR F hmass ζ ζ₀ hζ hζ₀ _ B₀ hB hBoundary hdet hD
  filter_upwards [hk] with i hi
  intro f g hf hg he hM
  have hn : ¬ ∃ r ∈ Ioc 0 R, f r ≠ 0 ∨ g r ≠ 0 := by
    intro hne
    obtain ⟨v,hv,hfix⟩ := radialMatchedPhysical_pencil (s i) ell i (z i) (hX i) (hm i)
      R _ hR F (hw i) (hp i) (ha i) (ζ i) f g hf hg he hne (M i) hM
    exact hv (hi v hfix)
  intro r hr
  constructor
  · by_contra h
    exact hn ⟨r,hr,Or.inl h⟩
  · by_contra h
    exact hn ⟨r,hr,Or.inr h⟩

end DefocusingNLS

end OAI

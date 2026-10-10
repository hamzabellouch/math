import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundaryJetLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedMultiplierLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobinLimit

namespace OAI

/-! Actual matched mass, transport and gauge factors preserve Robin convergence. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedBoundaryOperator_tendsto
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : innerBoundaryRadius < R)
    (M : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : Tendsto M atTop (𝓝 M₀)) :
    Tendsto (fun i => spectralFluxBoundary R
      (radialMatchedMassFunction (s i) (z i) R)
      (radialMatchedTransportFunction (s i) (z i) R)
      (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
        (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop
      (𝓝 (spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
        (radialMatchedFreeTransportFunction z₀ R)
        (spectralGaugeRobin (radialShootingFreeExterior z₀ R)
          (deriv (radialShootingFreeExterior z₀) R) M₀))) := by
  have hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1] : 0 < innerBoundaryRadius).trans hR
  have hμ : Tendsto (fun i => radialMatchedMassFunction (s i) (z i) R) atTop
      (𝓝 (radialMatchedFreeMassFunction z₀ R)) :=
    (radialMatched_mass_uniform_limit s hs z z₀ hz hX hm R).tendsto_at ⟨hR₀.le,le_rfl⟩
  have hA : Tendsto (fun i => radialMatchedTransportFunction (s i) (z i) R) atTop
      (𝓝 (radialMatchedFreeTransportFunction z₀ R)) := by
    have ht := (radialMatchedWeightedFlux_uniform_limit s hs z z₀ hz hX hm R hR₀.le).tendsto_at
      (show R ∈ Icc 0 R from ⟨hR₀.le,le_rfl⟩)
    exact ht.congr' (Eventually.of_forall (fun i =>
      radialMatchedWeightedFlux_average_nonneg (s i) (z i) (hX i) (hm i) R hR₀.le))
  have hq : Tendsto (fun i => radialMatchedProfile (s i) (z i) R) atTop
      (𝓝 (radialShootingFreeExterior z₀ R)) := by
    simpa only [radialMatchedFreeProfile,ite_eq_right (not_le.mpr hR)] using
      (radialMatchedProfile_uniform_limit s hs z z₀ hz R).tendsto_at
        (show R ∈ Icc 0 R from ⟨hR₀.le,le_rfl⟩)
  have hne : radialShootingFreeExterior z₀ R ≠ 0 := by
    simpa only [radialMatchedFreeProfile,ite_eq_right (not_le.mpr hR)] using
      radialMatchedFreeProfile_ne_zero s hs z z₀ hz R hR₀.le
  exact spectralGaugeFluxBoundary_tendsto R _ _ _ _ _ _ _ _ M M₀ hμ hA hq
    (radialMatchedProfile_deriv_tendsto s hs z z₀ hz hX hm R hR) hM hne

end DefocusingNLS

end OAI

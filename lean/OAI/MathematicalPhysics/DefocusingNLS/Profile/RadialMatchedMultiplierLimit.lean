import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousMultiplier

namespace OAI

/-! The mass and transport multipliers of the actual matched family. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedMassFunction (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  ‖radialMatchedProfile n z r‖^2

noncomputable def radialMatchedTransportFunction (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  (6-2*radialShootingA n)*(r*radialAverage (radialMatchedMassFunction n z) r)

noncomputable def radialMatchedFreeMassFunction (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  ‖radialMatchedFreeProfile z r‖^2

noncomputable def radialMatchedFreeTransportFunction (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  6*(r*radialAverage (radialMatchedFreeMassFunction z) r)

theorem radialMatchedMassFunction_continuous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) : Continuous (radialMatchedMassFunction n z) :=
  (radialMatchedProfile_differentiable n z hX hm).continuous.norm.pow 2

theorem radialMatchedTransportFunction_continuous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hm : radialMatchingMap n z=0) : Continuous (radialMatchedTransportFunction n z) :=
  continuous_const.mul (continuous_id.mul
    (continuous_radialAverage _ (radialMatchedMassFunction_continuous n z hX hm)))

variable (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatchedFreeMassFunction_continuous : Continuous (radialMatchedFreeMassFunction z₀) :=
  (radialMatchedFreeProfile_continuous s hs z z₀ hz hX hm).norm.pow 2

theorem radialMatchedFreeTransportFunction_continuous :
    Continuous (radialMatchedFreeTransportFunction z₀) :=
  continuous_const.mul (continuous_id.mul
    (continuous_radialAverage _ (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm)))

theorem radialMatched_massMultiplier_tendsto (R : ℝ) :
    Tendsto (fun i => spectralRadialWeightMultiplier R
      (spectralContinuousCoefficient R (radialMatchedMassFunction (s i) (z i))
        (radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i)))) atTop
      (𝓝 (spectralRadialWeightMultiplier R
        (spectralContinuousCoefficient R (radialMatchedFreeMassFunction z₀)
          (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm)))) := by
  apply spectralContinuousMultiplier_tendsto
  exact radialMatched_mass_uniform_limit s hs z z₀ hz hX hm R

theorem radialMatched_transportMultiplier_tendsto (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun i => spectralRadialWeightMultiplier R
      (spectralContinuousCoefficient R (radialMatchedTransportFunction (s i) (z i))
        (radialMatchedTransportFunction_continuous (s i) (z i) (hX i) (hm i)))) atTop
      (𝓝 (spectralRadialWeightMultiplier R
        (spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z₀)
          (radialMatchedFreeTransportFunction_continuous s hs z z₀ hz hX hm)))) := by
  apply spectralContinuousMultiplier_tendsto
  have ht := radialMatchedWeightedFlux_uniform_limit s hs z z₀ hz hX hm R hR
  exact ht.congr (Eventually.of_forall (fun i r hr =>
    radialMatchedWeightedFlux_average_nonneg (s i) (z i) (hX i) (hm i) r hr.1))

end DefocusingNLS

end OAI

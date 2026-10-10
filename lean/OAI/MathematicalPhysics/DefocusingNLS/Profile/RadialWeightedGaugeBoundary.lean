import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedGaugeBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDivergence

namespace OAI

/-! The actual profiles transfer the already-proved Liouville boundary decay
to the frequency-weighted gauge Cauchy energy. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatched_weighted_gauge_boundary_limit (R : ℝ) (hR : 0 < R)
    (omega : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (F G f g : ℕ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r))=(F i r,G i r))
    (henergy : Tendsto (fun i => R^11*spectralWeightedCauchyEnergy (omega i) (F i) (G i) R)
      atTop (𝓝 0)) :
    Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0) := by
  obtain ⟨c,_,hc,_,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  obtain ⟨D,_,hd⟩ := radialMatched_uniform_derivative_bound s hs z z₀ hz hX hm R hR
  have ht := henergy.const_mul (1+D^2/c)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hw.eventually (eventually_ge_atTop 1)] with i hi
    have he := spectralWeightedCauchyEnergy_nonneg (omega i) (by linarith) (f i) (g i) R
    exact mul_nonneg (by dsimp only [radialMassDensity]; positivity) he
  · filter_upwards [hb,hd,hw.eventually (eventually_ge_atTop 1)] with i hi hdi hoi
    have hQi := (radialMatchedEvenProfile_contDiff (s i) (z i) (hX i) (hm i)).differentiable
      (by simp)
    have hci : c ≤ ‖radialMatchedEvenProfile (s i) (z i) R‖^2 := by
      simpa only [radialMatchedEvenProfile_nonneg (s i) (z i) R hR.le] using (hi R ⟨hR.le,le_rfl⟩).1
    have he := spectralWeightedGaugeBoundary_le (omega i) c D R hoi hc
      (radialMatchedEvenProfile (s i) (z i)) (f i) (g i) (F i) (G i)
      hQi.differentiableAt ((hf i).differentiable (by norm_num)).differentiableAt
      ((hg i).differentiable (by norm_num)).differentiableAt (hpair i) hci (hdi R ⟨hR,le_rfl⟩)
    have he' := mul_le_mul_of_nonneg_left he (pow_nonneg hR.le 11)
    simpa only [radialMassDensity,radialMatchedEvenProfile_nonneg (s i) (z i) R hR.le,
      mul_assoc,mul_left_comm] using he'

end DefocusingNLS

end OAI

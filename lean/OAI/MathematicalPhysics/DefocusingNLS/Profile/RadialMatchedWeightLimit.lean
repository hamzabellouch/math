import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUniformWeightBounds

namespace OAI

/-! Positive limiting and uniformly coercive mass weights for the actual matched family. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
  (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatchedFreeProfile_continuous : Continuous (radialMatchedFreeProfile z₀) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r < 1
  · have hgeo := radialShooting_geometry (profileMatchingParameter z₀)
    have he : radialMatchedFreeProfile z₀ =ᶠ[𝓝 r] (fun _ => 1) := by
      filter_upwards [Iio_mem_nhds hr] with t ht
      change t < 1 at ht
      have htl : t ≤ radialShootingR (profileMatchingParameter z₀) := by linarith [hgeo.2.1]
      have htb : t ≤ innerBoundaryRadius := htl.trans hgeo.2.2.2.1
      simp only [radialMatchedFreeProfile,ite_eq_left htb,ite_eq_left htl]
    exact continuousAt_const.congr_of_eventuallyEq he
  · exact (radialMatchedFreeProfile_continuousOn s hs z z₀ hz hX hm (r+1)).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))

theorem radialMatchedFree_spectral_weight (R : ℝ) :
    ∃ w : SpectralHarmonicWeight R,
      w.density=(fun r => ‖radialMatchedFreeProfile z₀ r‖^2) ∧ ∃ c : ℝ, 0 < c ∧
      (∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r) ∧
      (∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) := by
  apply spectralPositiveWeight_exists
  · exact (radialMatchedFreeProfile_continuous s hs z z₀ hz hX hm).norm.pow 2
  · intro r hr
    exact sq_pos_of_pos (norm_pos_iff.mpr (radialMatchedFreeProfile_ne_zero s hs z z₀ hz r hr.1))

theorem radialMatched_uniform_weight_bounds (R : ℝ) :
    ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
      (∀ r ∈ Icc 0 R, c ≤ ‖radialMatchedFreeProfile z₀ r‖^2 ∧
        ‖‖radialMatchedFreeProfile z₀ r‖^2‖ ≤ M) ∧
      ∀ᶠ i in atTop, ∀ r ∈ Icc 0 R, c ≤ ‖radialMatchedProfile (s i) (z i) r‖^2 ∧
        ‖‖radialMatchedProfile (s i) (z i) r‖^2‖ ≤ M := by
  apply spectralUniform_positive_bounds R
    (fun i r => ‖radialMatchedProfile (s i) (z i) r‖^2)
    (fun r => ‖radialMatchedFreeProfile z₀ r‖^2)
    ((radialMatchedFreeProfile_continuousOn s hs z z₀ hz hX hm R).norm.pow 2)
  · intro r hr
    exact sq_pos_of_pos (norm_pos_iff.mpr (radialMatchedFreeProfile_ne_zero s hs z z₀ hz r hr.1))
  · exact radialMatched_mass_uniform_limit s hs z z₀ hz hX hm R

end DefocusingNLS

end OAI

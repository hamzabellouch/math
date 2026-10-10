import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalMap
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierInversion

namespace OAI

/-! # Exact physical meaning of the localization operator

The map into the completed homogeneous space represents the actual cutoff
χ(y/L)v(y) at every point, not only almost everywhere in Fourier variables.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_expandingPhysicalLocalization (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) : Continuous (expandingPhysicalLocalization a k L χ f) := by
  rw [expandingPhysicalLocalization_eq_series a k L ha ha1 hk hL]
  exact continuous_localizedFourierSeries L χ _
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f)

/-- The completed-space localization is pointwise the cutoff of the actual torus function. -/
theorem homogeneousLocalization_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousLocalizationCLM a k L ha ha1 hk hL χ f) y =
        expandingPhysicalLocalization a k L χ f y := by
  have hAE := (homogeneousLocalization_ae a k L ha ha1 hk hL χ f).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  have hF := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk
    (memLp_expandingPhysicalLocalization_fourier a k L ha ha1 hk hL χ f)).1
  change inverseRadianFourier (homogeneousLocalization a k L ha ha1 hk hL χ f) y = _
  rw [inverseRadianFourier_congr_ae hAE]
  exact inverseRadianFourier_radianFourier_of_integrable
    (continuous_expandingPhysicalLocalization a k L ha ha1 hk hL χ f)
    (integrable_expandingPhysicalLocalization a k L ha ha1 hk hL χ f) hF y

end DefocusingNLS

end OAI

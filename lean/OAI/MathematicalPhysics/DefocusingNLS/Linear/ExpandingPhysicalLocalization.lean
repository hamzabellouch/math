import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierSeries
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingTorus
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDerivatives

namespace OAI

/-! # The actual torus cutoff in Euclidean coordinates

This identifies the Euclidean Fourier-series localization with χ(y/L)v(y)
for the previously constructed continuous function on the expanding torus.
-/

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def euclideanToTorus (y : E) : SchrodingerTorus :=
  fun j => (y j : AddCircle (2 * Real.pi))

theorem torusCharacter_euclidean (n : frequencyLattice) (y : E) :
    torusCharacter n (euclideanToTorus y) = spatialFourierCharacter n y := by
  have hcoordinate (j : Fin 12) :
      fourier (frequencyCoordinates n j) (y j : AddCircle (2 * Real.pi)) =
        Complex.exp (((y j * (n : E) j : ℝ) : ℂ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    have hn : (frequencyCoordinates n j : ℂ) = (((n : E) j : ℝ) : ℂ) := by
      exact_mod_cast frequencyCoordinates_coe n j
    rw [hn]
    push_cast
    field_simp
  change (∏ j : Fin 12, fourier (frequencyCoordinates n j)
    (y j : AddCircle (2 * Real.pi))) = _
  simp_rw [hcoordinate]
  rw [← Complex.exp_sum]
  unfold spatialFourierCharacter
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial]

/-- χ(y/L) times the genuine continuous expanding-torus function. -/
noncomputable def expandingPhysicalLocalization (a k L : ℝ) (χ : 𝓢(E, ℂ))
    (f : FourierL2) (y : E) : ℂ :=
  χ (L⁻¹ • y) * expandingTorusFunction a k L f (euclideanToTorus (L⁻¹ • y))

theorem expandingPhysicalLocalization_eq_series (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingPhysicalLocalization a k L χ f =
      localizedFourierSeries L χ (expandingFourierCoefficient a k L f) := by
  funext y
  unfold expandingPhysicalLocalization localizedFourierSeries spatialFourierSeries
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  simp only [torusCharacter_euclidean]

theorem integrable_expandingPhysicalLocalization (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) : Integrable (expandingPhysicalLocalization a k L χ f) := by
  rw [expandingPhysicalLocalization_eq_series a k L ha ha1 hk hL]
  exact integrable_localizedFourierSeries L (by linarith) χ _
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f)

end DefocusingNLS

end OAI

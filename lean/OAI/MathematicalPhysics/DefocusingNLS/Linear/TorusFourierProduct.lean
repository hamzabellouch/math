import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFourierTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusL2Coefficient

namespace OAI

/-! # Absolutely convergent Fourier multiplication in physical L² -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance torusFourierProductMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusFourierProductProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusFourierIsometry_convolution (a : frequencyLattice → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (f : FourierL2) :
    torusFourierIsometry (fourierConvolution a f) =
      torusL2Product (∑' n, a n • UnitAddTorus.mFourier (frequencyCoordinates n))
        (torusFourierIsometry f) := by
  have hs : Summable (fun n => a n • UnitAddTorus.mFourier (frequencyCoordinates n)) := by
    apply Summable.of_norm
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using ha
  have hleft := (summable_fourierConvolution_terms a ha f).hasSum.mapL
    torusFourierIsometry.toContinuousLinearEquiv.toContinuousLinearMap
  have hright := hs.hasSum.mapL (torusL2Coefficient (torusFourierIsometry f))
  have he : (fun n => torusFourierIsometry (a n • fourierTranslation n f)) =
      (fun n => torusL2Coefficient (torusFourierIsometry f)
        (a n • UnitAddTorus.mFourier (frequencyCoordinates n))) := by
    funext n
    rw [map_smul, map_smul, torusL2Coefficient_apply, torusFourierIsometry_translation]
  apply hleft.unique
  change HasSum (fun n => torusFourierIsometry (a n • fourierTranslation n f)) _
  rw [he]
  exact hright

theorem torusFourierIsometry_expanding_convolution (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q f : FourierL2) :
    torusFourierIsometry (fourierConvolution (expandingFourierCoefficient a k L q) f) =
      torusL2Product (expandingUnitTorusFunction a k L q) (torusFourierIsometry f) := by
  exact torusFourierIsometry_convolution _
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL q) f

end DefocusingNLS

end OAI

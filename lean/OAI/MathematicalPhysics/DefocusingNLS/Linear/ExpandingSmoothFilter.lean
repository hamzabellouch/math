import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierBoundedMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFourierConvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalConvolution

namespace OAI

/-! # Schwartz convolution is the exact smooth Fourier filter on expanding tori -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingPhysicalContinuous (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) : C(E, ℂ) where
  toFun y := spatialFourierSeries (expandingFourierCoefficient a k L f) (L⁻¹ • y)
  continuous_toFun := (continuous_spatialFourierSeries _
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f)).comp
      (continuous_const_smul L⁻¹)

theorem expandingPhysicalContinuous_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (y : E) :
    expandingPhysicalContinuous a k L ha ha1 hk hL f y =
      expandingTorusFunction a k L f (euclideanToTorus (L⁻¹ • y)) := by
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  simp only [expandingPhysicalContinuous, ContinuousMap.coe_mk, spatialFourierSeries,
    torusCharacter_euclidean]

theorem expandingPhysicalContinuous_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (y : E) :
    ‖expandingPhysicalContinuous a k L ha ha1 hk hL f y‖ ≤ expandingEmbeddingBound a k * ‖f‖ := by
  rw [expandingPhysicalContinuous_apply]
  exact expandingTorusFunction_point_bound a k L ha ha1 hk hL f _

noncomputable def expandingSchwartzFilter (L : ℝ) (K : 𝓢(E, ℂ)) : FourierL2 →L[ℂ] FourierL2 :=
  fourierBoundedMultiplier (∫ z : E, ‖K z‖) (integral_nonneg (fun _ => norm_nonneg _))
    (fun n : frequencyLattice => radianFourierKernel K (L⁻¹ • (n : E)))
    (fun _ => radianFourierKernel_norm_le_integral K _)

@[simp] theorem expandingSchwartzFilter_apply (L : ℝ) (K : 𝓢(E, ℂ))
    (f : FourierL2) (n : frequencyLattice) :
    expandingSchwartzFilter L K f n = radianFourierKernel K (L⁻¹ • (n : E)) * f n := rfl

theorem expandingSchwartzFilter_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (K : 𝓢(E, ℂ)) (f : FourierL2) (y : E) :
    expandingPhysicalContinuous a k L ha ha1 hk hL (expandingSchwartzFilter L K f) y =
      ∫ z : E, K z * expandingPhysicalContinuous a k L ha ha1 hk hL f (y - z) := by
  change spatialFourierSeries (expandingFourierCoefficient a k L (expandingSchwartzFilter L K f))
    (L⁻¹ • y) = _
  have he : expandingFourierCoefficient a k L (expandingSchwartzFilter L K f) =
      fun n : frequencyLattice => radianFourierKernel K (L⁻¹ • (n : E)) *
        expandingFourierCoefficient a k L f n := by
    funext n
    exact expandingFourierCoefficient_multiplier a k L _ _ _ _ f n
  rw [he]
  exact schwartzFourierConvolution_eq L K _
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f) y

theorem expandingSchwartzFilter_ball (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (K : 𝓢(E, ℂ)) (f : FourierL2) (y : Metric.closedBall (0 : E) R) :
    expandingPhysicalContinuous a k L ha ha1 hk hL (expandingSchwartzFilter L K f) y =
      schwartzBallConvolution R K (expandingPhysicalContinuous a k L ha ha1 hk hL f) y := by
  rw [expandingSchwartzFilter_physical, schwartzBallConvolution_apply R
    (expandingEmbeddingBound a k * ‖f‖) (by unfold expandingEmbeddingBound; positivity)]
  exact expandingPhysicalContinuous_norm_le a k L ha ha1 hk hL f

end DefocusingNLS

end OAI

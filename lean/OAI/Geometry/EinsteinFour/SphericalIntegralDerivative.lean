import OAI.Geometry.EinsteinFour.SphericalRotation
import OAI.Geometry.EinsteinFour.ContinuousFieldDerivative

namespace OAI

/-! Differentiating a continuous family on the compact sphere commutes with
its normalized integral when the pointwise derivative is jointly continuous. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

local instance sphericalIntegralNormedGroup : NormedAddCommGroup C(Directions, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance sphericalIntegralNormedSpace : NormedSpace ℝ C(Directions, ℝ) :=
  ContinuousMap.normedSpace

variable [IsProbabilityMeasure sphereMeasure]

private def sphericalIntegralLinear : C(Directions, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ q, f q ∂sphereMeasure
  map_add' f g := by
    change (∫ q, f q + g q ∂sphereMeasure) = _
    exact integral_add (sphere_continuous_integrable f.continuous)
      (sphere_continuous_integrable g.continuous)
  map_smul' a f := by
    change (∫ q, a * f q ∂sphereMeasure) = a * ∫ q, f q ∂sphereMeasure
    exact integral_const_mul a _

def sphericalIntegralCLM : C(Directions, ℝ) →L[ℝ] ℝ :=
  sphericalIntegralLinear.mkContinuous 1 (fun f => by
    change ‖∫ q, f q ∂sphereMeasure‖ ≤ 1 * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := sphereMeasure)
      (Filter.Eventually.of_forall (fun q => f.norm_coe_le_norm q)))

theorem sphereIntegral_hasDerivAt {F G : ℝ → C(Directions, ℝ)}
    (hG : Continuous (fun p : ℝ × Directions => G p.1 p.2))
    (hpoint : ∀ t q, HasDerivAt (fun s => F s q) (G t q) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ q, F s q ∂sphereMeasure)
      (∫ q, G t q ∂sphereMeasure) t := by
  exact sphericalIntegralCLM.hasFDerivAt.comp_hasDerivAt t
    (Averages.continuousField_hasDerivAt_of_joint hG hpoint t)

end
end PositiveEinsteinFour.Angular

end OAI

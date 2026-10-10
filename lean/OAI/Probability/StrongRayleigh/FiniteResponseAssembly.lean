import OAI.Probability.StrongRayleigh.ResponseDerivative
import OAI.Probability.StrongRayleigh.ResponseDirectional
import OAI.Probability.StrongRayleigh.ResponseLipschitz
import OAI.Probability.StrongRayleigh.CovarianceRow
import OAI.Probability.StrongRayleigh.ElementaryResponse

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

theorem finite_response_of_covariance_signs {F : Type u_1} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool))
    (hoff : ∀ (i j : F) (h : F → ℝ), i ≠ j → tiltCovariance μ h i j ≤ 0)
    (hrow : ∀ (i : F) (h : F → ℝ), 0 ≤ ∑ j : F, tiltCovariance μ h i j) :
    (∀ (i j : F) (h : F → ℝ),
      HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
        (tiltCovariance μ h i j) 0) ∧
    (∀ (i : F) (h : F → ℝ),
      (∑ j : F, |tiltCovariance μ h i j|) ≤
        2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
      2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
    (∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
      (∀ j : F, |h j - h' j| ≤ D) →
      |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  have hbound (i : F) (h : F → ℝ) :
      (∑ j : F, |tiltCovariance μ h i j|) ≤
        2 * tiltMean μ h i * (1 - tiltMean μ h i) := by
    have hb := sum_abs_row_le_twice_diag (tiltCovariance μ h i) i
      (tiltCovariance_self_nonneg μ h i)
      (fun j hj => hoff i j h (Ne.symm hj)) (hrow i h)
    simpa only [tiltCovariance_self, mul_assoc] using hb
  refine ⟨fun i j h => tiltMean_hasDerivAt_coordinate μ h i j,
    fun i h => ⟨hbound i h, twice_tilt_variance_le_half μ h i⟩, ?_⟩
  intro i h h' D hD hdist
  have hb := finite_response_lipschitz_of_directional_deriv
    (fun h => tiltMean μ h i) (fun h => tiltCovariance μ h i) ((1 : ℝ) / 2)
    (fun h v t => tiltMean_hasDerivAt_affine μ h v i t)
    (fun h => (hbound i h).trans (twice_tilt_variance_le_half μ h i))
    h h' D hD hdist
  convert hb using 1
  ring

end Problem336AdditiveD139

end

end OAI

import OAI.Geometry.RCD.Harmonic.ProjectionResidualValues
import OAI.Geometry.RCD.Harmonic.MetricQuadraticError

namespace OAI

/-! # Actual centered coordinate bounds on the projection region -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- The existing metric approximation supplies the physical coordinate
value estimate used in the two-center projection. The bound is uniform
in the scale, frame, and covector. -/
theorem projection_coordinate_values {n : ℕ} {p : X} {s epsilon : ℝ}
    (hs : 0 < s) (hepsilon : epsilon ≤ 1)
    (u : Fin n → SobolevSpace μ hQ) (V : X → Euclidean n)
    (N : Euclidean n ≃L[ℝ] Euclidean n) (hcenter : V p = 0)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[
      μ.restrict (ball p (s / 512))] fun x => V x j)
    (hmetric : IsPointedApproximation p 0 (s / 64) 4 epsilon
      (fun x => (s / 64)⁻¹ • (N : Euclidean n →L[ℝ] Euclidean n).adjoint (V x))) :
    ∀ b : Euclidean n, ∀ᵐ x ∂μ.restrict (ball p (s / 512)),
      |SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)) x| ≤ s * ‖b‖ := by
  have hvalue : ∀ᵐ x ∂μ.restrict (ball p (s / 512)),
      ‖(N : Euclidean n →L[ℝ] Euclidean n).adjoint (V x)‖ ≤ 1 * s := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hdist : dist x p ≤ 4 * (s / 64) := by
      have hx' := mem_ball.mp hx
      linarith
    have hn := (hmetric.centered_norm_error (by positivity : 0 < s / 64)
      (by norm_num) (by rw [hcenter, map_zero, smul_zero]) hdist).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : 0 < s / 64))] at hn
    have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ s / 64)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : s / 64 ≠ 0), one_mul] at hh
    have hb := mul_le_mul_of_nonneg_left hepsilon hs.le
    nlinarith only [hh, hb, hs]
  intro b
  simpa only [one_mul] using framed_coordinate_value_bound μ hQ (ball p (s / 512))
    u V N hrep hvalue b

end RegularPointCoordinates

end

end OAI

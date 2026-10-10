import OAI.Geometry.EinsteinFour.ChartMetricTransition
import OAI.Geometry.EinsteinFour.ChartMetricNondegeneracy
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The local metric volume density and its exact coordinate change law.
Identification with the metric Hausdorff measure is a separate step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

private theorem sqrt_det_congruence (G J : Mat4) :
    Real.sqrt (Jᵀ * (G * J)).det = |J.det| * Real.sqrt G.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have he : J.det * (G.det * J.det) = J.det ^ 2 * G.det := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartVolumeDensity (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  Real.sqrt (metricInChart g c z).det

theorem chartVolumeDensity_pos (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : 0 < chartVolumeDensity g c z :=
  Real.sqrt_pos.mpr (metricInChart_posDef g c z hz).det_pos

theorem chartVolumeDensity_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (chartVolumeDensity g c) z := by
  have hd : ContDiffAt ℝ ∞ (fun w => (metricInChart g c w).det) z := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    exact contDiffAt_const.mul
      (contDiffAt_prod fun i _ => metricInChart_contDiffAt g c z hz (σ i) i)
  exact hd.sqrt (metricInChart_posDef g c z hz).det_pos.ne'

/-- The density transforms by the absolute determinant of the actual
derivative of the chart transition. -/
theorem chartVolumeDensity_transition (g : SmoothMetric M) (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    chartVolumeDensity g c z = |(chartTransitionMatrix c d z).det| *
      chartVolumeDensity g d (chartTransition c d z) := by
  unfold chartVolumeDensity
  rw [metricInChart_transition g c d z hz hx]
  exact sqrt_det_congruence _ _

/-- In orthonormal frame coordinates the metric density cancels the
absolute determinant of the frame matrix. -/
theorem chartVolumeDensity_mul_frame_det (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (E : Mat4)
    (hE : Eᵀ * metricInChart g c z * E = 1) :
    chartVolumeDensity g c z * |E.det| = 1 := by
  have hd : (metricInChart g c z).det * E.det ^ 2 = 1 := by
    have he := congrArg Matrix.det hE
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at he
    calc
      _ = E.det * (metricInChart g c z).det * E.det := by ring
      _ = 1 := he
  have hs := congrArg Real.sqrt hd
  rw [Real.sqrt_mul (metricInChart_posDef g c z hz).det_pos.le,
    Real.sqrt_sq_eq_abs, Real.sqrt_one] at hs
  exact hs

end
end PositiveEinsteinFour.Geometry

end OAI

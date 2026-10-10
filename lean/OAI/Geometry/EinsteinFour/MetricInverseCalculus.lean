import OAI.Geometry.EinsteinFour.ChartMetricNondegeneracy
import OAI.Geometry.EinsteinFour.CurvatureMetricSkew

namespace OAI

/-! The inverse metric is parallel. Its coordinate derivative is derived
from the inverse identity and the proved metric compatibility equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

private theorem inverse_metric_derivative_algebra (G H C D : Mat4)
    (hGH : G * H = 1) (hHG : H * G = 1)
    (hD : D * G + H * (Cᵀ * G + G * C) = 0) :
    D = -(C * H) - H * Cᵀ := by
  have h := congrArg (fun A : Mat4 => A * H) hD
  have hexpand : (D * G + H * (Cᵀ * G + G * C)) * H = D + H * Cᵀ + C * H := by
    calc
      _ = D * (G * H) + (H * Cᵀ) * (G * H) + (H * G) * (C * H) := by
        noncomm_ring
      _ = _ := by rw [hGH, hHG]; simp
  rw [hexpand, zero_mul] at h
  have hd : D = -(H * Cᵀ + C * H) :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using h)
  rw [hd]
  abel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrixPartial_inverseMetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    matrixPartial (fun w => (metricInChart g c w)⁻¹) i z =
      -(connectionMatrix g c i z * (metricInChart g c z)⁻¹) -
        (metricInChart g c z)⁻¹ * (connectionMatrix g c i z)ᵀ := by
  let G := metricInChart g c
  let H := fun w => (G w)⁻¹
  have hdet : (G z).det ≠ 0 := (metricInChart_posDef g c z hz).det_pos.ne'
  have hG : IsUnit (G z).det := isUnit_iff_ne_zero.mpr hdet
  have hdG (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (metricInChart_contDiffAt g c z hz r s).differentiableAt (by simp)
  have hdH (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_inv_contDiffAt g c z hz hdet r s).differentiableAt (by simp)
  have he : (fun w => H w * G w) =ᶠ[𝓝 z] (fun _ => 1) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (metricInChart_posDef g c w hw).det_pos.ne')
  have hprod := matrixPartial_congr he i
  rw [matrixPartial_mul H G z hdH hdG i] at hprod
  have hc : matrixPartial (fun _ : FourSpace => (1 : Mat4)) i z = 0 := by
    ext r s
    simp [matrixPartial, partialDeriv]
  rw [hc, matrixPartial_metric g c z hG i] at hprod
  exact inverse_metric_derivative_algebra (G z) (H z) (connectionMatrix g c i z)
    (matrixPartial H i z) (Matrix.mul_nonsing_inv _ hG) (Matrix.nonsing_inv_mul _ hG) hprod

end
end PositiveEinsteinFour.Geometry

end OAI

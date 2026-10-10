import OAI.Probability.SLE.Geometry.InteriorFluxBound
import OAI.Probability.SLE.Geometry.AnalyticCircleSquare
import OAI.Probability.SLE.Geometry.ExteriorLaplacianTest

namespace OAI

/-! The first Taylor coefficient is bounded by the signed area of a
holomorphic disk map. No injectivity of the disk map is needed. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian

namespace SLEExactGauge

lemma analytic_norm_sq_laplacian {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    (Δ (fun w => ‖f w‖^2)) z=4*‖deriv f z‖^2 := by
  have hh := laplacian_holomorphic_comp hf
    ((contDiff_id.norm_sq ℝ : ContDiff ℝ 2 (fun w : ℂ => ‖w‖^2)).contDiffAt)
  simpa only [Function.comp_def,id_eq,complex_laplacian_norm_sq,mul_comm] using hh

lemma analytic_flux_ge_first_coefficient {f : ℂ → ℂ} {R : ℝ}
    (hR : 0<R) (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) R)) :
    4*Real.pi*R^2*‖deriv f 0‖^2≤
      ∫ θ in -Real.pi..Real.pi, radialLaplacianFlux (fun z => ‖f z‖^2) (R,θ) := by
  have hu (z : ℂ) (hz : z∈closedBall (0:ℂ) R) :
      ContDiffAt ℝ 2 (fun z => ‖f z‖^2) z :=
    (hf z hz).contDiffAt.restrict_scalars ℝ |>.norm_sq ℝ
  have hAvg (r : ℝ) (hr : r∈Icc 0 R) :
      4*‖deriv f 0‖^2≤circleAverage (Δ (fun z => ‖f z‖^2)) 0 r := by
    have hd : AnalyticOnNhd ℂ (deriv f) (closedBall (0:ℂ) |r|) :=
      hf.deriv.mono (closedBall_subset_closedBall (by rw [abs_of_nonneg hr.1]; exact hr.2))
    have hb := analytic_circleAverage_norm_sq_ge hd
    have he : circleAverage (Δ (fun z => ‖f z‖^2)) 0 r=
        circleAverage (fun z => (4:ℝ)*‖deriv f z‖^2) 0 r := by
      apply circleAverage_congr_sphere
      intro z hz
      apply analytic_norm_sq_laplacian
      exact hf z ((closedBall_subset_closedBall (by rw [abs_of_nonneg hr.1]; exact hr.2))
        (sphere_subset_closedBall hz))
    rw [he]
    have hmul : circleAverage (fun z => (4:ℝ)*‖deriv f z‖^2) 0 r=
        4*circleAverage (fun z => ‖deriv f z‖^2) 0 r := by
      simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (4:ℝ))
        (f := fun z => ‖deriv f z‖^2) (c := (0:ℂ)) (R := r))
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hh := radial_flux_ge_of_circle_laplacian hR hu hAvg
  convert! hh using 1; ring

end SLEExactGauge

end

end OAI

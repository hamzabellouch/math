import OAI.Geometry.CylinderCovering.Singular.HessianDefinitions
import OAI.Geometry.CylinderCovering.Singular.Stream
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section

namespace CylinderCovering.SingularStream
open RuledApproximation Set Filter
open scoped Topology ContDiff

theorem potentialGradient_eq (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    potentialGradient p z = matrixCLM 0 1 (-1) 0 (singularField p z) := by
  have hv : vec2 (z 0) (z 1) = z := by
    ext i
    fin_cases i <;> simp [vec2]
  have hb := potential_deriv_b p (z 0) hz
  have hr := potential_neg_deriv_r p (z 0) hz
  rw [hv] at hb hr
  simp only [potentialGradient, matrixCLM_apply, zero_mul, one_mul, neg_one_mul,
    zero_add, add_zero, hb]
  congr 1
  linarith

theorem potentialHessian_eq (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    potentialHessian p z =
      (matrixCLM 0 1 (-1) 0).comp (fderiv ℝ (singularField p) z) := by
  have hd := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  have hc := (matrixCLM 0 1 (-1) 0).hasFDerivAt.comp z hd.hasFDerivAt
  have he : (fun w => matrixCLM 0 1 (-1) 0 (singularField p w)) =ᶠ[𝓝 z]
      potentialGradient p := by
    have hpos : ∀ᶠ w : Plane in 𝓝 z, 0 < w 1 :=
      (isOpen_lt continuous_const (by fun_prop : Continuous (fun w : Plane => w 1))).mem_nhds hz
    filter_upwards [hpos] with w hw
    exact (potentialGradient_eq p hw).symm
  exact (hc.congr_of_eventuallyEq he.symm).fderiv

theorem potentialHessian_det (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    LinearMap.det (potentialHessian p z).toLinearMap =
      LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap := by
  rw [potentialHessian_eq p hz]
  change LinearMap.det ((matrixCLM 0 1 (-1) 0).toLinearMap.comp
    (fderiv ℝ (singularField p) z).toLinearMap) = _
  rw [LinearMap.det_comp, matrixCLM_det]
  norm_num

theorem potentialHessian_det_formula (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    LinearMap.det (potentialHessian p z).toLinearMap =
      (z 1 / (1 / 2 : ℝ)) ^ (2 * p - 4) * (p - 1) / 2 *
        ((2 - p) * (z 0 / z 1) ^ 2 - p) := by
  rw [potentialHessian_det p hz, (singularField_trace_det p hz).2]
  have hp : (z 1 / (1 / 2 : ℝ)) ^ (2 * p - 4) =
      ((z 1 / (1 / 2 : ℝ)) ^ (p - 2)) ^ (2 : ℕ) := by
    rw [show 2 * p - 4 = (p - 2) * (2 : ℕ) by norm_num; ring]
    exact Real.rpow_mul_natCast (by positivity) (p - 2) 2
  rw [hp]

theorem potentialHessian_det_neg {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {z : Plane} (hz : 0 < z 1) (hcone : |z 0| ≤ z 1) :
    LinearMap.det (potentialHessian p z).toLinearMap < 0 := by
  rw [potentialHessian_det p hz]
  exact (singularField_hyperbolic hp hp2 hz hcone).2

end CylinderCovering.SingularStream

end

end OAI

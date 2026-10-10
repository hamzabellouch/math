import OAI.Geometry.EinsteinFour.MetricInverseCalculus

namespace OAI

/-! Differentiate contraction by the actual inverse metric. This is the
local identity needed to commute covariant differentiation with trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem partialDeriv_matrix_trace (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ r, DifferentiableAt ℝ (fun w => A w r r) z) (i : Fin 4) :
    partialDeriv (fun w => (A w).trace) i z = (matrixPartial A i z).trace := by
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun r w => A w r r) (fun r _ => hA r)
  change fderiv ℝ (fun w => ∑ r, A w r r) z (coordinateVector i) =
    ∑ r, fderiv ℝ (fun w => A w r r) z (coordinateVector i)
  rw [hd, _root_.sum_apply]

private theorem metric_trace_derivative_algebra (H C T D : Mat4) :
    (((-(C * H) - H * Cᵀ) * T + H * D).trace) =
      (H * (D - Cᵀ * T - T * C)).trace := by
  have hm : (-(C * H) - H * Cᵀ) * T + H * D =
      H * (D - Cᵀ * T - T * C) + (H * T * C - C * H * T) := by
    noncomm_ring
  have hcycle : (C * H * T).trace = (H * T * C).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm C (H * T)
  rw [hm, Matrix.trace_add, Matrix.trace_sub, hcycle,
    sub_self, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partialDeriv_metric_contraction (g : SmoothMetric M) (c : M)
    (T : FourSpace → Mat4) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hT : ∀ r s, DifferentiableAt ℝ (fun w => T w r s) z) (i : Fin 4) :
    partialDeriv (fun w => ((metricInChart g c w)⁻¹ * T w).trace) i z =
      ((metricInChart g c z)⁻¹ *
        (matrixPartial T i z - (connectionMatrix g c i z)ᵀ * T z -
          T z * connectionMatrix g c i z)).trace := by
  let H := fun w => (metricInChart g c w)⁻¹
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  have hH (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_inv_contDiffAt g c z hz hdet r s).differentiableAt (by simp)
  have hprod (r : Fin 4) : DifferentiableAt ℝ (fun w => (H w * T w) r r) z := by
    change DifferentiableAt ℝ (fun w => ∑ s, H w r s * T w s r) z
    exact DifferentiableAt.fun_sum (fun s _ => (hH r s).mul (hT s r))
  rw [partialDeriv_matrix_trace (fun w => H w * T w) z hprod i,
    matrixPartial_mul H T z hH hT i, matrixPartial_inverseMetric g c z hz i]
  exact metric_trace_derivative_algebra _ _ _ _

end
end PositiveEinsteinFour.Geometry

end OAI

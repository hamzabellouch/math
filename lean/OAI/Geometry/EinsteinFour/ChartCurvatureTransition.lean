import OAI.Geometry.EinsteinFour.ChartConnectionTransition
import OAI.Geometry.EinsteinFour.WeightedConnectionCurvature

namespace OAI

/-! Differentiating the actual Christoffel transformation gives the
curvature intertwining equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartWeightedConnection (g : SmoothMetric M) (c d : M) (i : Fin 4)
    (z : FourSpace) : Mat4 :=
  weightedConnection (chartTransitionMatrix c d z)
    (fun a => connectionMatrix g d a (chartTransition c d z)) i

theorem chartWeightedConnection_contDiffAt (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (i r s : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartWeightedConnection g c d i w r s) z := by
  have ht := (chartAt FourSpace d).map_source hx
  have hdet := (metricInChart_posDef g d _ ht).det_pos.ne'
  change ContDiffAt ℝ ∞ (fun w => ∑ a, chartTransitionMatrix c d w a i *
    christoffel g d (chartTransition c d w) r a s) z
  apply ContDiffAt.sum
  intro a _
  have hC : ContDiffAt ℝ ∞ (fun w : FourSpace => christoffel g d w r a s)
      (chartTransition c d z) :=
    christoffel_contDiffAt g d _ ht hdet r a s
  have hcomp : ContDiffAt ℝ ∞
      (fun w => christoffel g d (chartTransition c d w) r a s) z :=
    hC.comp z (chartTransition_contDiffAt c d z hz hx)
  exact (chartTransitionMatrix_contDiffAt c d z hz hx a i).mul
    hcomp

theorem chartWeightedConnection_partial (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartWeightedConnection g c d j) i z =
      weightedConnectionDerivative (chartTransitionMatrix c d z)
        (fun r => matrixPartial (chartTransitionMatrix c d) r z)
        (fun a => connectionMatrix g d a (chartTransition c d z))
        (fun b a => matrixPartial (connectionMatrix g d a) b (chartTransition c d z)) i j := by
  let F := chartTransition c d
  let J := chartTransitionMatrix c d
  let A := fun a w => connectionMatrix g d a (F w)
  have ht : F z ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hx
  have hdet := (metricInChart_posDef g d _ ht).det_pos.ne'
  have hF : DifferentiableAt ℝ F z :=
    (chartTransition_contDiffAt c d z hz hx).differentiableAt (by simp)
  have hJ (a : Fin 4) : DifferentiableAt ℝ (fun w => J w a j) z :=
    (chartTransitionMatrix_contDiffAt c d z hz hx a j).differentiableAt (by simp)
  have hC (a r s : Fin 4) : DifferentiableAt ℝ
      (fun w => connectionMatrix g d a w r s) (F z) :=
    (christoffel_contDiffAt g d _ ht hdet r a s).differentiableAt (by simp)
  have hA (a r s : Fin 4) : DifferentiableAt ℝ (fun w => A a w r s) z :=
    (hC a r s).comp z hF
  change matrixPartial (fun w => ∑ a, J w a j • A a w) i z = _
  rw [matrixPartial_sum_four (fun a w => J w a j • A a w) z
    (fun a r s => (hJ a).mul (hA a r s)) i]
  have hs (a : Fin 4) : matrixPartial (fun w => J w a j • A a w) i z =
      partialDeriv (fun w => J w a j) i z • A a z + J z a j • matrixPartial (A a) i z :=
    matrixPartial_smul _ _ z (hJ a) (hA a) i
  have hc (a : Fin 4) : matrixPartial (A a) i z =
      ∑ b, J z b i • matrixPartial (connectionMatrix g d a) b (F z) :=
    matrixPartial_comp hF (hC a) i
  simp only [hs, hc]
  rfl

theorem chart_connection_intertwining (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    chartTransitionMatrix c d z * connectionMatrix g c i z =
      matrixPartial (chartTransitionMatrix c d) i z +
        chartWeightedConnection g c d i z * chartTransitionMatrix c d z := by
  have he : connectionMatrix g c i z = pulledChartConnection g c d z i := by
    ext r s
    exact christoffel_transition g c d z hz hx r i s
  rw [he]
  exact pulledConnection_equation _ _ _
    (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))

theorem chart_connection_intertwining_derivative (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartTransitionMatrix c d) i z * connectionMatrix g c j z +
      chartTransitionMatrix c d z * matrixPartial (connectionMatrix g c j) i z =
      matrixPartial (matrixPartial (chartTransitionMatrix c d) j) i z +
        matrixPartial (chartWeightedConnection g c d j) i z * chartTransitionMatrix c d z +
          chartWeightedConnection g c d j z * matrixPartial (chartTransitionMatrix c d) i z := by
  let J := chartTransitionMatrix c d
  have hcnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have hcs : ContinuousAt (chartAt FourSpace c).symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := I4) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas c) hz).continuousAt
  have hdnear : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    hcs.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hx)
  have he : (fun w => J w * connectionMatrix g c j w) =ᶠ[𝓝 z]
      (fun w => matrixPartial J j w + chartWeightedConnection g c d j w * J w) := by
    filter_upwards [hcnear, hdnear] with w hcw hdw
    exact chart_connection_intertwining g c d w hcw hdw j
  have hJ (r s : Fin 4) : ContDiffAt ℝ ∞ (fun w => J w r s) z :=
    chartTransitionMatrix_contDiffAt c d z hz hx r s
  have hC (r s : Fin 4) : DifferentiableAt ℝ (fun w => connectionMatrix g c j w r s) z :=
    (christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
      r j s).differentiableAt (by simp)
  have hU (r s : Fin 4) : DifferentiableAt ℝ
      (fun w => chartWeightedConnection g c d j w r s) z :=
    (chartWeightedConnection_contDiffAt g c d z hz hx j r s).differentiableAt (by simp)
  have hP (r s : Fin 4) : DifferentiableAt ℝ (fun w => matrixPartial J j w r s) z :=
    (((hJ r s).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hprod (r s : Fin 4) : DifferentiableAt ℝ
      (fun w => (chartWeightedConnection g c d j w * J w) r s) z := by
    change DifferentiableAt ℝ (fun w => ∑ p,
      chartWeightedConnection g c d j w r p * J w p s) z
    exact DifferentiableAt.fun_sum (fun p _ => (hU r p).mul
      ((hJ p s).differentiableAt (by simp)))
  have h := matrixPartial_congr he i
  rw [matrixPartial_mul J (connectionMatrix g c j) z
      (fun r s => (hJ r s).differentiableAt (by simp)) hC i,
    matrixPartial_add (matrixPartial J j) (fun w => chartWeightedConnection g c d j w * J w)
      z hP hprod i,
    matrixPartial_mul (chartWeightedConnection g c d j) J z hU
      (fun r s => (hJ r s).differentiableAt (by simp)) i] at h
  simpa only [add_assoc] using h

theorem chart_curvature_intertwining (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    chartTransitionMatrix c d z * coordinateCurvatureMatrix g c i j z =
      (matrixPartial (chartWeightedConnection g c d j) i z -
        matrixPartial (chartWeightedConnection g c d i) j z +
          chartWeightedConnection g c d i z * chartWeightedConnection g c d j z -
            chartWeightedConnection g c d j z * chartWeightedConnection g c d i z) *
              chartTransitionMatrix c d z := by
  have hcomm := matrixPartial_comm (chartTransitionMatrix c d) z
    (chartTransitionMatrix_contDiffAt c d z hz hx) i j
  exact curvature_intertwining_of_connection _ _ _ _ _ _ _ _ _ _ _ _
    (chart_connection_intertwining g c d z hz hx i)
    (chart_connection_intertwining g c d z hz hx j)
    (chart_connection_intertwining_derivative g c d z hz hx i j)
    (by simpa only [hcomm] using
      chart_connection_intertwining_derivative g c d z hz hx j i)

theorem chartWeightedConnection_curvature (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartWeightedConnection g c d j) i z -
        matrixPartial (chartWeightedConnection g c d i) j z +
      chartWeightedConnection g c d i z * chartWeightedConnection g c d j z -
        chartWeightedConnection g c d j z * chartWeightedConnection g c d i z =
      ∑ a, ∑ b, (chartTransitionMatrix c d z a i * chartTransitionMatrix c d z b j) •
        coordinateCurvatureMatrix g d a b (chartTransition c d z) := by
  rw [chartWeightedConnection_partial g c d z hz hx,
    chartWeightedConnection_partial g c d z hz hx]
  simpa only [chartWeightedConnection, coordinateCurvatureMatrix] using
    weightedConnection_curvature (chartTransitionMatrix c d z)
      (fun r => matrixPartial (chartTransitionMatrix c d) r z)
      (fun a => connectionMatrix g d a (chartTransition c d z))
      (fun b a => matrixPartial (connectionMatrix g d a) b (chartTransition c d z))
      (fun r s t => jacobian_partials_commute (chartTransition_contDiffAt c d z hz hx) t r s)
      i j

/-- The actual (1,3)-curvature in two overlapping metric charts. -/
theorem coordinateCurvatureMatrix_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    coordinateCurvatureMatrix g c i j z = (chartTransitionMatrix c d z)⁻¹ *
      (∑ a, ∑ b, (chartTransitionMatrix c d z a i * chartTransitionMatrix c d z b j) •
        coordinateCurvatureMatrix g d a b (chartTransition c d z)) *
          chartTransitionMatrix c d z := by
  have h := congrArg (fun A : Mat4 => (chartTransitionMatrix c d z)⁻¹ * A)
    (chart_curvature_intertwining g c d z hz hx i j)
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr
    (chartTransitionMatrix_det_ne_zero g c d z hz hx)),
    chartWeightedConnection_curvature g c d z hz hx i j] at h
  simpa only [Matrix.mul_assoc] using h

end
end PositiveEinsteinFour.Geometry

end OAI

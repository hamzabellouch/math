import OAI.Geometry.EinsteinFour.ChartMetricNondegeneracy

namespace OAI

/-! The actual metric pullback matrix in a chart. The tangent coordinates
at the image point use its own centered chart, so this congruence is the
zeroth-order part of the curvature coordinate-change calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartInverseMatrix (c : M) (z : FourSpace) : Mat4 :=
  fun i j => (show FourSpace from
    mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector j)) i

theorem metricInChart_eq_center_congruence (g : SmoothMetric M) (c : M)
    (z : FourSpace) :
    metricInChart g c z = (chartInverseMatrix c z)ᵀ *
      (chartMetric g ((chartAt FourSpace c).symm z) * chartInverseMatrix c z) := by
  ext i j
  symm
  change (fun k => chartInverseMatrix c z k i) ⬝ᵥ
    (chartMetric g ((chartAt FourSpace c).symm z) *ᵥ
      (fun k => chartInverseMatrix c z k j)) = _
  rw [chartMetric_pairing]
  rfl

def chartTransition (c d : M) (z : FourSpace) : FourSpace :=
  chartAt FourSpace d ((chartAt FourSpace c).symm z)

def chartTransitionMatrix (c d : M) (z : FourSpace) : Mat4 :=
  fun i j => fderiv ℝ (chartTransition c d) z (coordinateVector j) i

theorem chartTransition_contDiffAt (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (chartTransition c d) z := by
  have hc : ContMDiffAt I4 I4 ∞ (chartAt FourSpace c).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hz
  have hd : ContMDiffAt I4 I4 ∞ (chartAt FourSpace d) ((chartAt FourSpace c).symm z) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hx
  exact (hd.comp z hc).contDiffAt

theorem chartTransition_fderiv (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (chartTransition c d) z =
      (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm z)).comp
        (mfderiv I4 I4 (chartAt FourSpace c).symm z) := by
  have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c).symm z :=
    (mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hz
  have hd : MDifferentiableAt I4 I4 (chartAt FourSpace d)
      ((chartAt FourSpace c).symm z) :=
    (mdifferentiable_chart (I := I4) d).mdifferentiableAt hx
  convert! mfderiv_comp z hd hc using 1
  rw [mfderiv_eq_fderiv]
  rfl

theorem metricInChart_transition (g : SmoothMetric M) (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    metricInChart g c z = (chartTransitionMatrix c d z)ᵀ *
      (metricInChart g d (chartTransition c d z) * chartTransitionMatrix c d z) := by
  let A : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm z)
  let B : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d z)
  let C : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  have hBA : B.comp A = ContinuousLinearMap.id ℝ FourSpace :=
    (mdifferentiable_chart (I := I4) d).symm_comp_deriv hx
  have hF : fderiv ℝ (chartTransition c d) z = A.comp C :=
    chartTransition_fderiv c d z hz hx
  have hc : B.comp (fderiv ℝ (chartTransition c d) z) = C := by
    rw [hF, ← ContinuousLinearMap.comp_assoc, hBA, ContinuousLinearMap.id_comp]
  have hv (i : Fin 4) : B (fderiv ℝ (chartTransition c d) z (coordinateVector i)) =
      C (coordinateVector i) := congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
        L (coordinateVector i)) hc
  ext i j
  symm
  change (fun k => chartTransitionMatrix c d z k i) ⬝ᵥ
    (metricInChart g d (chartTransition c d z) *ᵥ
      (fun k => chartTransitionMatrix c d z k j)) = _
  rw [metricInChart_pairing]
  change g.inner ((chartAt FourSpace d).symm (chartTransition c d z))
    (B (fderiv ℝ (chartTransition c d) z (coordinateVector i)))
    (B (fderiv ℝ (chartTransition c d) z (coordinateVector j))) = _
  rw [hv, hv]
  have hi : (chartAt FourSpace d).symm (chartTransition c d z) =
      (chartAt FourSpace c).symm z := (chartAt FourSpace d).left_inv hx
  rw [hi]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI

import OAI.Geometry.EinsteinFour.ConnectionPullback

namespace OAI

/-! The connection coordinate change is derived from the actual metric
pullback, using metric compatibility and zero torsion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def pulledChartConnection (g : SmoothMetric M) (c d : M) (z : FourSpace)
    (i : Fin 4) : Mat4 :=
  pulledConnection (chartTransitionMatrix c d z)
    (matrixPartial (chartTransitionMatrix c d) i z)
    (weightedConnection (chartTransitionMatrix c d z)
      (fun a => connectionMatrix g d a (chartTransition c d z)) i)

theorem chartTransitionMatrix_det_ne_zero (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    (chartTransitionMatrix c d z).det ≠ 0 := by
  intro he
  have h := congrArg Matrix.det (metricInChart_transition g c d z hz hx)
  simp only [Matrix.det_mul, Matrix.det_transpose, he, zero_mul] at h
  exact (metricInChart_posDef g c z hz).det_pos.ne' h

theorem chartTransitionMatrix_contDiffAt (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (r s : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartTransitionMatrix c d w r s) z :=
  jacobian_entry_contDiffAt (chartTransition_contDiffAt c d z hz hx) r s

theorem matrixPartial_transition_target_metric (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    matrixPartial (fun w => metricInChart g d (chartTransition c d w)) i z =
      (weightedConnection (chartTransitionMatrix c d z)
        (fun a => connectionMatrix g d a (chartTransition c d z)) i)ᵀ *
          metricInChart g d (chartTransition c d z) +
      metricInChart g d (chartTransition c d z) *
        weightedConnection (chartTransitionMatrix c d z)
          (fun a => connectionMatrix g d a (chartTransition c d z)) i := by
  have hf := (chartTransition_contDiffAt c d z hz hx).differentiableAt (by simp)
  have htarget : chartTransition c d z ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hx
  have hG : IsUnit (metricInChart g d (chartTransition c d z)).det :=
    isUnit_iff_ne_zero.mpr (metricInChart_posDef g d _ htarget).det_pos.ne'
  rw [matrixPartial_comp hf (fun r s =>
    (metricInChart_contDiffAt g d _ htarget r s).differentiableAt (by simp))]
  simp only [matrixPartial_metric g d _ hG]
  simp only [weightedConnection, Matrix.transpose_sum, Matrix.transpose_smul,
    Finset.sum_mul, Finset.mul_sum, smul_add, smul_mul_assoc, mul_smul_comm,
    Finset.sum_add_distrib]
  rfl

theorem pulledChartConnection_metric (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    matrixPartial (metricInChart g c) i z =
      (pulledChartConnection g c d z i)ᵀ * metricInChart g c z +
        metricInChart g c z * pulledChartConnection g c d z i := by
  let J := chartTransitionMatrix c d
  let H := fun w => metricInChart g d (chartTransition c d w)
  let U := weightedConnection (J z)
    (fun a => connectionMatrix g d a (chartTransition c d z)) i
  have hG : metricInChart g c z = (J z)ᵀ * (H z * J z) :=
    metricInChart_transition g c d z hz hx
  have hcnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have hcs : ContinuousAt (chartAt FourSpace c).symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := I4) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas c) hz).continuousAt
  have hdnear : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    hcs.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hx)
  have heq : metricInChart g c =ᶠ[𝓝 z] (fun w => (J w)ᵀ * (H w * J w)) := by
    filter_upwards [hcnear, hdnear] with w hcw hdw
    exact metricInChart_transition g c d w hcw hdw
  have hj (r s : Fin 4) : DifferentiableAt ℝ (fun w => J w r s) z :=
    (chartTransitionMatrix_contDiffAt c d z hz hx r s).differentiableAt (by simp)
  have ht : chartTransition c d z ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hx
  have hh (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_contDiffAt g d _ ht r s).differentiableAt (by simp) |>.comp z
      ((chartTransition_contDiffAt c d z hz hx).differentiableAt (by simp))
  have hpartial : matrixPartial H i z = Uᵀ * H z + H z * U :=
    matrixPartial_transition_target_metric g c d z hz hx i
  have hunit : IsUnit (J z).det :=
    isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx)
  rw [matrixPartial_congr heq, matrixPartial_congruence J H z hj hh, hpartial]
  have hk := pulledConnection_metric_compatibility (H z) (J z)
    (matrixPartial J i z) U hunit
  rw [← Matrix.mul_assoc] at hG
  rw [hG]
  exact hk.symm

theorem pulledChartConnection_torsion (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (i j k : Fin 4) :
    pulledChartConnection g c d z i k j = pulledChartConnection g c d z j k i := by
  unfold pulledChartConnection
  apply pulledConnection_torsion (chartTransitionMatrix c d z)
    (fun r => matrixPartial (chartTransitionMatrix c d) r z)
    (fun a => connectionMatrix g d a (chartTransition c d z))
  · intro r s t
    exact jacobian_partials_commute (chartTransition_contDiffAt c d z hz hx) t r s
  · intro r s t
    exact christoffel_comm g d (chartTransition c d z) t r s

theorem christoffel_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (k i j : Fin 4) :
    christoffel g c z k i j = pulledChartConnection g c d z i k j := by
  have hG : IsUnit (metricInChart g c z).det :=
    isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'
  have he := christoffel_eq_of_compatible g c z hG
    (fun r s t => pulledChartConnection g c d z s r t)
    (fun r s t => pulledChartConnection_torsion g c d z hz hx s t r) ?_
  · exact (congrFun (congrFun (congrFun he k) i) j).symm
  · intro r s t
    have hm := congrArg (fun A : Mat4 => A s t)
      (pulledChartConnection_metric g c d z hz hx r)
    simp only [matrixPartial, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] at hm
    rw [← Finset.sum_add_distrib] at hm
    rw [hm]
    apply Finset.sum_congr rfl
    intro p _
    rw [metricInChart_comm g c z p t]
    ring

end
end PositiveEinsteinFour.Geometry

end OAI

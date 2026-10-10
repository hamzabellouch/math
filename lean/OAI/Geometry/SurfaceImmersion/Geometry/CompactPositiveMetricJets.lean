import OAI.Geometry.SurfaceImmersion.Geometry.CompactPositiveTensorBound
import OAI.Geometry.SurfaceImmersion.Atlas.ConvexQuadraticPhase

namespace OAI

/-! The closed family of first metric jets with a fixed positive lower
bound is compact. It therefore fixes the connection bound before any
finite-point modification or choice of disk centers. -/
noncomputable section
open Set Metric
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes PhaseMean

def positiveMetricJetRegion (c B : ℝ) : Set MetricFirstJet :=
  {j | ‖j‖ ≤ B ∧ ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v}

lemma positiveMetricJetRegion_compact (c B : ℝ) :
    IsCompact (positiveMetricJetRegion c B) := by
  have hclosed : IsClosed {j : MetricFirstJet | ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold evaluate
    fun_prop
  have heq : positiveMetricJetRegion c B =
      closedBall (0 : MetricFirstJet) B ∩ {j | ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v} := by
    ext j
    simp only [positiveMetricJetRegion,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
  rw [heq]
  exact (isCompact_closedBall _ _).inter_right hclosed

lemma positiveMetricJetRegion_det {c B : ℝ} (hc : 0 < c)
    {j : MetricFirstJet} (hj : j ∈ positiveMetricJetRegion c B) : metricJetDet j ≠ 0 := by
  have hp : ∀ v : Base, v ≠ 0 → 0 < evaluate j.1 v v := by
    intro v hv
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hj.2 v)
  exact ((tensor_positive_iff j.1).mp hp).2.ne'

theorem uniform_positive_metric_connection {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : MetricFirstJet,
      ‖j‖ ≤ B → (∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v) →
      ∀ i, ‖metricConnectionAt j i‖ ≤ D := by
  obtain ⟨D,hD,hb⟩ := compact_metricConnection_bound
    (positiveMetricJetRegion_compact c B)
    (fun _ hj => positiveMetricJetRegion_det hc hj)
  exact ⟨D,hD,fun j hj hpos => hb j ⟨hj,hpos⟩⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI

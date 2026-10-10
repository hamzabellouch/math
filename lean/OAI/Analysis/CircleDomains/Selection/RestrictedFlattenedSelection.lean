import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection

namespace OAI

/-! Keep the large disk needed for the compact source cutoff and restrict
the same selection to the smaller disk on which that cutoff equals one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def FlattenedSourceSelection.restrictWorking
    (M : CompactScalarModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L L' δ ε : ℝ} {H : ControlledHeight R d}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε) (hL : L' ≤ L) :
    FlattenedSourceSelection M H Wold A L' δ ε := by
  let U := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  let V := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L'
  have hVU : V ⊆ U := inter_subset_inter_right _ (ball_subset_ball hL)
  have hμ : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono hVU le_rfl
  have hsupport := (M.horizontalSection_plane_memLp hG hinf L).norm.indicator
    (MeasurableSet.iUnion (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet))
  refine {
    oldValues := S.oldValues, old_open := S.old_open, oldWitness := S.oldWitness
    old_close := S.old_close, old_error := S.old_error
    heightValues := S.heightValues, height_open := S.height_open, heightWitness := S.heightWitness
    height_close := S.height_close, height_error := S.height_error
    center := S.center, center_outside := S.center_outside, target := S.target
    target_projection := S.target_projection, radius := S.radius, radius_pos := S.radius_pos
    radius_tendsto := S.radius_tendsto, cutoff := S.cutoff, cutoff_smooth := S.cutoff_smooth
    cutoff_support := S.cutoff_support, cutoff_unit := S.cutoff_unit, value := S.value
    value_eq := S.value_eq, priority_continuous := S.priority_continuous
    priority_error_memLp := S.priority_error_memLp.mono_measure hμ
    priority_error := ?_, support_error := ?_
    old_constant := S.old_constant, height_constant := S.height_constant }
  · exact (ENNReal.toReal_mono S.priority_error_memLp.eLpNorm_ne_top
      (eLpNorm_mono_measure _ hμ)).trans_lt S.priority_error
  · exact (ENNReal.toReal_mono hsupport.eLpNorm_ne_top
      (eLpNorm_mono_measure _ hμ)).trans_lt S.support_error

end CompactScalarModel
end CircleDomainRigidity

end

end OAI

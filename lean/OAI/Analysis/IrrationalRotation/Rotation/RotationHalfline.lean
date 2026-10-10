import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.FieldKoopmanGenerated
import OAI.Analysis.IrrationalRotation.Analysis.FieldHalflineNonmembership

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.Rotation

theorem shiftedPullback_mem_unitary (θ : ℝ) (m : ℤ) :
    DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (action θ m) (action_measurePreserving θ m) ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  apply FieldKoopman.operator_mem_unitary (WeightedShift.shift m)
    (action θ m) (action θ (-m)) (action_measurePreserving θ m)
    (action_measurePreserving θ (-m))
  · funext x
    simp [action, add_assoc]
  · funext x
    simp [action, add_assoc]

theorem V_commute_shiftedPullback (θ : ℝ) (m : ℤ) :
    Commute (V θ) (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (action θ m) (action_measurePreserving θ m)) := by
  unfold V representation
  apply FieldKoopman.commute_fieldDiagonal
  apply Filter.Eventually.of_forall
  intro x k
  change character (action θ (k-m) (action θ m x)) = character (action θ k x)
  congr 1
  simp only [action, sub_zsmul]
  abel

theorem commute_shiftedPullback_of_mem_algebra (θ : ℝ) (m : ℤ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (action θ m) (action_measurePreserving θ m)) := by
  apply FieldKoopman.commute_of_mem_generated_of_unitary ({U, V θ} : Set _)
    (shiftedPullback_mem_unitary θ m) _ hT
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hA | hA
  · subst A
    exact FieldKoopman.commute_fieldShifts 1 m _ _
  · have hA' : A = V θ := Set.mem_singleton_iff.mp hA
    subst A
    exact V_commute_shiftedPullback θ m

theorem fieldTailProjection_not_mem_algebra (θ : ℝ) (m : ℤ) :
    WeightedShift.fieldTailProjection (μ := circleMeasure) m ∉ algebra θ := by
  intro h
  exact WeightedShift.fieldTailProjection_not_commute_shiftedPullback m
    (action θ 1) (action_measurePreserving θ 1)
    (commute_shiftedPullback_of_mem_algebra θ 1 h)

theorem exists_ordinary_invariant_projection_outside_algebra
    (θ : ℝ) (a : C(Circle, ℂ)) :
    ∃ p : Hilbert →L[ℂ] Hilbert, IsStarProjection p ∧ p ≠ 0 ∧ p ≠ 1 ∧
      (1-p) * weighted θ a * p = 0 ∧ p ∉ algebra θ := by
  refine ⟨WeightedShift.fieldTailProjection 0,
    WeightedShift.isStarProjection_fieldTailProjection 0,
    WeightedShift.fieldTailProjection_ne_zero 0,
    WeightedShift.fieldTailProjection_ne_one 0, ?_, fieldTailProjection_not_mem_algebra θ 0⟩
  exact WeightedShift.fieldTailProjection_invariant (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
    (fun k => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable) 0

end Invariant233.Rotation

end

end OAI

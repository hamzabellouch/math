import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorStability
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Uniform operator tolerance on bounded finite coefficient data. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance operatorToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {ι : Type*} [Fintype ι]

theorem finite_primitive_operator_tolerance (D : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ z z' : PrimitiveOperatorData ι, ‖z‖ ≤ D → ‖z'-z‖ < eps →
        ‖primitiveDataOperator z'-primitiveDataOperator z‖ < eta := by
  have hc := (isCompact_closedBall (0 : PrimitiveOperatorData ι) (D+1)).uniformContinuousOn_of_continuous
    primitiveDataOperator_smooth.continuous.continuousOn
  obtain ⟨eps,heps,hnear⟩ := Metric.uniformContinuousOn_iff.mp hc eta heta
  refine ⟨min eps 1,lt_min heps zero_lt_one,min_le_right _ _,?_⟩
  intro z z' hz hdist
  have hzK : z ∈ Metric.closedBall 0 (D+1) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hzK' : z' ∈ Metric.closedBall 0 (D+1) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    have hh : ‖z'-z‖ < 1 := hdist.trans_le (min_le_right _ _)
    calc
      ‖z'‖ ≤ ‖z'-z‖+‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ D+1 := by linarith
  simpa only [dist_eq_norm] using hnear z' hzK' z hzK
    (by simpa only [dist_eq_norm] using hdist.trans_le (min_le_left _ _))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

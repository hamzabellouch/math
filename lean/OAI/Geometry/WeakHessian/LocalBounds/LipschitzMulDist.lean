import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.CdLogMidpointBall
import OAI.Geometry.WeakHessian.LocalBounds.DistDecayCover

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_mul_dist (o : X) (a : ℝ) :
    LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |a*dist x o-a*dist y o| ≤ |a| * dist x y
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)

lemma CurvatureDimension.exists_entropy_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) : ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  let d := |C|+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hCd : C < d := by dsimp [d]; linarith [le_abs_self C]
  have hvol := cd_ball_volume_bound hN hcd hfull hfin o
  have hbase : MemLp (fun x => Real.exp (-(d*dist x o))) 2 m := by
    simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le
      (show C < 2*d by linarith) hvol
  refine ⟨2*d,by positivity,?_,?_,?_⟩
  · simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*d by linarith) hvol
  · simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*(2*d) by linarith) hvol
  · apply (hbase.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*d*dist x o)*Real.exp (-(2*d*dist x o))| ≤ |2*Real.exp (-(d*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      have H := (Real.mul_exp_neg_le_exp_neg_one (d*dist x o)).trans
        (show Real.exp (-1) ≤ 1 by rw [Real.exp_le_one_iff]; norm_num)
      have he : (2*d*dist x o)*Real.exp (-(2*d*dist x o)) =
          2*(d*dist x o*Real.exp (-(d*dist x o)))*Real.exp (-(d*dist x o)) := by
        rw [show -(2*d*dist x o) = -(d*dist x o)+(-(d*dist x o)) by ring,Real.exp_add]
        ring
      rw [he]
      nlinarith [Real.exp_pos (-(d*dist x o))]
end WeakHessian

end
end InlinedFile0

end OAI

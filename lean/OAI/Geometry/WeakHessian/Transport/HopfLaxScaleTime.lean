import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap

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
namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma hopfLax_scale_time (f : X →ᵇ ℝ) {b : ℝ} (hb : 0 < b) (x : X) :
    b*hopfLax ((1/b) • f) b x = hopfLax f 1 x := by
  have h0 : b ≠ 0 := hb.ne'
  have hlo (g : X →ᵇ ℝ) (y : X) : -‖g‖ ≤ g y := (boundedContinuous_bounds g y).1
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (hlo f) (by norm_num : (0:ℝ) < 1) x
  obtain ⟨z,hz⟩ := exists_hopf_minimizer ((1/b) • f).continuous (hlo ((1/b) • f)) hb x
  have heq (w : X) : b*hopfObjective ((1/b) • f) b x w = hopfObjective f 1 x w := by
    simp only [hopfObjective,BoundedContinuousFunction.smul_apply,smul_eq_mul]
    field_simp
  apply le_antisymm
  · calc
      b*hopfLax ((1/b) • f) b x ≤ b*hopfObjective ((1/b) • f) b x y :=
        mul_le_mul_of_nonneg_left (hopfLax_le_objective (hlo ((1/b) • f)) hb x y) hb.le
      _ = hopfLax f 1 x := (heq y).trans hy
  · rw [← hz,heq]
    exact hopfLax_le_objective (hlo f) (by norm_num) x z
end WeakHessianTransport
end
end InlinedFile0

end OAI

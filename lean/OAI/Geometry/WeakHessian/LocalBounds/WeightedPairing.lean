import Mathlib

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
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma weighted_pairing {V f g : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hg : MemLp (fun x => g x*Real.exp (-V x)) 2 m) :
    Integrable (fun x => f x*g x) m ∧ ‖∫ x,f x*g x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖hg.toLp (fun x => g x*Real.exp (-V x))‖ := by
  have he (x : X) : (f x*Real.exp (V x))*(g x*Real.exp (-V x)) = f x*g x := by
    calc
      _ = (f x*g x)*(Real.exp (V x)*Real.exp (-V x)) := by ring
      _ = _ := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  refine ⟨(hf.integrable_mul hg).congr (ae_of_all _ he),?_⟩
  have hin : (∫ x,f x*g x ∂m) =
      ⟪hf.toLp (fun x => f x*Real.exp (V x)),hg.toLp (fun x => g x*Real.exp (-V x))⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x h1 h2
    rw [h1,h2]
    simp only [RCLike.inner_apply,conj_trivial]
    convert (he x).symm using 1
    ring
  rw [hin]
  exact norm_inner_le_norm _ _
end WeakHessian

end
end InlinedFile0

end OAI

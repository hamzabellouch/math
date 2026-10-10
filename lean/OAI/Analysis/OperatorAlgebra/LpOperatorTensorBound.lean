import OAI.Analysis.WeakInfiniteness.TensorFunctoriality
import Mathlib.MeasureTheory.Function.L2Space
import OAI.Analysis.OperatorAlgebra.LpAlgebraicInstances

namespace OAI

/-! An abstract Hilbert-space operator estimate transfers to the canonical
algebraic structures on the concrete L² space. -/
noncomputable section
open MeasureTheory
open scoped TensorProduct
namespace WeakPureInfiniteness

def hilbertOperatorTensorBound {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Type*} [Fintype I]
    (l r a b : I → K →L[ℂ] K) : Prop :=
  ‖∑ i, l i * r i‖ ≤ ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖

lemma lp_operator_tensor_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Fintype I]
    (l r a b : I → Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (h : hilbertOperatorTensorBound l r a b) :
    ‖∑ i, l i * r i‖ ≤ ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  unfold hilbertOperatorTensorBound at h
  convert h

end WeakPureInfiniteness

end

end OAI

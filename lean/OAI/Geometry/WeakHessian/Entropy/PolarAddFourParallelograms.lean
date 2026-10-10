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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
lemma polar_add_of_four_parallelograms {E : Type*} [AddCommGroup E]
    (q : E → ℝ) (x y z : E)
    (h₁ : q ((x+z)+y) + q ((x+z)-y) = 2*q (x+z)+2*q y)
    (h₂ : q ((x-z)+y) + q ((x-z)-y) = 2*q (x-z)+2*q y)
    (h₃ : q ((y+z)+x) + q ((y+z)-x) = 2*q (y+z)+2*q x)
    (h₄ : q ((y-z)+x) + q ((y-z)-x) = 2*q (y-z)+2*q x)
    (hn₁ : q (-(x-y-z)) = q (x-y-z))
    (hn₂ : q (-(x-y+z)) = q (x-y+z)) :
    (q ((x+y)+z)-q ((x+y)-z))/4 =
      (q (x+z)-q (x-z))/4 + (q (y+z)-q (y-z))/4 := by
  have e₁ : (x+z)+y = (x+y)+z := by abel
  have e₂ : (x+z)-y = x-y+z := by abel
  have e₃ : (x-z)+y = (x+y)-z := by abel
  have e₄ : (x-z)-y = x-y-z := by abel
  have e₅ : (y+z)+x = (x+y)+z := by abel
  have e₆ : (y+z)-x = -(x-y-z) := by abel
  have e₇ : (y-z)+x = (x+y)-z := by abel
  have e₈ : (y-z)-x = -(x-y+z) := by abel
  rw [e₁,e₂] at h₁
  rw [e₃,e₄] at h₂
  rw [e₅,e₆,hn₁] at h₃
  rw [e₇,e₈,hn₂] at h₄
  linarith
end WeakHessian

end
end InlinedFile0

end OAI

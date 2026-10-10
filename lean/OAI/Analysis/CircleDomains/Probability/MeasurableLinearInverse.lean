import OAI.Analysis.CircleDomains.Selection.RegularMapPieces
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! The inverse of a planar linear map, with zero at singular maps, is Borel measurable. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma measurable_planar_linear_inverse :
    Measurable (ContinuousLinearMap.inverse : (ℂ →L[ℝ] ℂ) → (ℂ →L[ℝ] ℂ)) := by
  classical
  let U : Set (ℂ →L[ℝ] ℂ) := {A | A.IsInvertible}
  have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hc : ContinuousOn ContinuousLinearMap.inverse U := by
    intro A hA
    exact (hA.contDiffAt_map_inverse (n := 0)).continuousAt.continuousWithinAt
  have hm := hc.measurable_piecewise (g := fun _ => (0 : ℂ →L[ℝ] ℂ)) continuousOn_const hU.measurableSet
  convert hm using 1
  funext A
  by_cases hA : A ∈ U
  · simp only [piecewise_eq_of_mem U _ _ hA]
  · rw [piecewise_eq_of_notMem U _ _ hA, ContinuousLinearMap.inverse_of_not_isInvertible hA]

end CircleDomainRigidity

end

end OAI

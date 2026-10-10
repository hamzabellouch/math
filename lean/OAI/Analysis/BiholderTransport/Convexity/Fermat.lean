import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

lemma isLocalMin_hasMFDerivAt_eq_zero {f : M → ℝ} {x : M}
    {L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ}
    (h : IsLocalMin f x) (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x L) : L = 0 := by
  let c := extChartAt 𝓘(ℝ,E) x
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source hx
  have hc : ContinuousAt c.symm (c x) :=
    ((continuousOn_extChartAt_symm x) _ hcx).continuousAt ((isOpen_extChartAt_target x).mem_nhds hcx)
  have hmin : IsLocalMin (fun w : E => f (c.symm w)) (c x) := by
    have hh : IsLocalMin f (c.symm (c x)) := by rw [c.left_inv hx]; exact h
    exact hh.comp_continuous hc
  have hDf : HasFDerivAt (fun w : E => f (c.symm w)) L (c x) := by
    convert! hD.2.hasFDerivAt (by simp only [mfld_simps,Filter.univ_mem])
  exact hmin.hasFDerivAt_eq_zero hDf

end WeakMTWTransport

end

end OAI

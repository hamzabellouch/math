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

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma IsLocalMin.mfderiv_eq_zero {f : M → ℝ} {x : M}
    (h : IsLocalMin f x) (hd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x = 0 := by
  let c := extChartAt 𝓘(ℝ,E) x
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (c.map_source hx))
  let F : E → ℝ := fun q => f (c.symm q)
  have hF : DifferentiableAt ℝ F (c x) := by
    have hd' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f (c.symm (c x)) := by
      rw [c.left_inv hx]; exact hd
    exact (hd'.comp (c x) (hc.mdifferentiableAt (by simp))).differentiableAt
  have hmin : IsLocalMin F (c x) := by
    have hc' : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      have H := hc.continuousAt.tendsto
      rw [c.left_inv hx] at H
      exact H
    filter_upwards [hc'.eventually h] with q hq
    simpa only [F,c.left_inv hx] using hq
  have hzero : HasFDerivAt F 0 (c x) :=
    hF.hasFDerivAt.congr_fderiv (hmin.hasFDerivAt_eq_zero hF.hasFDerivAt)
  have H := hzero.hasMFDerivAt.comp x
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (show x ∈ (chartAt E x).source from mem_chart_source E x)).hasMFDerivAt
  have heq : f =ᶠ[𝓝 x] (fun y : M => F (c y)) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) x] with y hy
    dsimp [F]; rw [c.left_inv hy]
  rw [(H.congr_of_eventuallyEq heq).mfderiv]
  ext v
  rfl

lemma upper_contact_mfderiv {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x)
    (hg : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) g x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y) (heq : f x=g x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x=mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) g x := by
  have hmin : IsLocalMin (fun y => g y-f y) x := by
    filter_upwards [hle] with y hy
    change g x-f x ≤ g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := IsLocalMin.mfderiv_eq_zero hmin (hg.sub hf)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (g-f) x = 0 at H
  rw [mfderiv_sub hg hf] at H
  exact (sub_eq_zero.mp H).symm

end WeakMTWTransport

end

end OAI

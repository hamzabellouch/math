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

namespace WeakMTWTransport

lemma exists_smooth_extension_near {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  let b : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let g : E → F := fun x => b x • f x
  have hbS : tsupport b ⊆ S := by
    rw [b.tsupport_eq]
    intro x hx
    apply hrS
    change dist x a < r
    have h : dist x a ≤ r/2 := hx
    linarith
  refine ⟨g,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact b.contDiff.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hbS hx)))
    · have heq : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change b y • f y = 0
        simp only [hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [b.eventuallyEq_one] with x hx
    change b x • f x = f x
    simpa only [Pi.one_apply,one_smul] using congrArg (fun z : ℝ => z • f x) hx

end WeakMTWTransport

end

end OAI

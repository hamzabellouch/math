import Mathlib
import OAI.Geometry.WeakMTW.Support.ActiveContinuation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def FirstScaleHypotheses (y : ι → M) (h : ι → ℝ) (s : ℝ) : Prop :=
   0 < s ∧ s < 1 ∧
     (∀ r : ℝ, 0 ≤ r → r < s → ∀ p ∈ activeHullGraph (n := n) y h,
       r • p.2 ∈ injectivityDomain p.1) ∧
     (∀ p ∈ activeHullGraph (n := n) y h, s • p.2 ∈ minimizingDomain p.1) ∧
     (∃ p ∈ activeHullGraph (n := n) y h, s • p.2 ∉ injectivityDomain p.1)

 theorem activeProjection_critical_local_injective (hMTW : HasWeakMTW (n := n) (M := M))
     (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : FirstScaleHypotheses (n := n) y h s) :
     ∀ q : ActivePoint (n := n) y h, ∃ U ∈ 𝓝 q, Set.InjOn (activeProjection y h s) U := by
   intro q
   exact ⟨univ,Filter.univ_mem,
     (activeProjection_critical_bijective y h hMTW hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1).1.injOn⟩
end
end WeakMTW
end

section

end

end WeakMTWGlobalSupport

end OAI

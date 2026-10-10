import Mathlib
import OAI.Geometry.WeakMTW.Convexity
import OAI.Geometry.WeakMTW.Potentials.IntermediateTheorem
import OAI.Geometry.WeakMTW.Support.CriticalLocalTheorem

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
section CurrentFullMain
variable {n : ℕ} (hn : 2 ≤ n) {M : Type*}
  [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
  [IsManifold (WeakMTW.model n) ∞ M]
  [CompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
  [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
    (fun x : M => TangentSpace (WeakMTW.model n) x)]
  [IsRiemannianManifold (WeakMTW.model n) M]
  (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
include hn hmtw

theorem current_foundation :
    (∀ u : M → ℝ, WeakMTW.IsPotential u → WeakMTW.GlobalSupportingProperty (n := n) u) ∧
    (∀ u v : M → ℝ, WeakMTW.IsDualPair u v → WeakMTW.ConvexLiftedSections (n := n) u v) ∧
    WeakMTW.IntermediateGeometry hmtw
 :=
  ⟨fun _u hu => WeakMTW.globalSupportingProperty hmtw hu,
    fun _u _v huv => WeakMTW.convexLiftedSections hmtw huv,
    current_intermediate_geometry hn hmtw⟩
end CurrentFullMain

theorem current_convexity_domains
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)) (x : M) :
    Convex ℝ (WeakMTW.minimizingDomain (n := n) x) ∧
    Convex ℝ (WeakMTW.injectivityDomain (n := n) x)
 :=
  ⟨WeakMTW.minimizingDomain_convex hmtw x, WeakMTW.injectivityDomain_convex hmtw x⟩

theorem current_all_scales
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (x : M) :
    s • WeakMTW.activeHull (n := n) y h x ⊆ WeakMTW.injectivityDomain x
 := by
  rintro w ⟨b,hb,rfl⟩
  exact WeakMTW.activeHull_scaled_mem_injectivity hmtw y h hs hs1 x hb

theorem current_segment_nonconjugacy
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
    (x : M) {v₀ v₁ : TangentSpace (WeakMTW.model n) x}
    (hseg : segment ℝ v₀ v₁ ⊆ WeakMTW.minimizingDomain x)
    (h₀ : WeakMTW.Nonconjugate x v₀) (h₁ : WeakMTW.Nonconjugate x v₁) :
    ∀ w ∈ segment ℝ v₀ v₁, WeakMTW.Nonconjugate x w
 := WeakMTW.segment_nonconjugacy hmtw x hseg h₀ h₁

theorem current_critical_local_injectivity
    {n : ℕ} (_hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → M) (h : ι → ℝ) {s : ℝ} (hs : WeakMTW.FirstScaleHypotheses (n := n) y h s) :
    ∀ q : WeakMTW.ActivePoint (n := n) y h, ∃ U ∈ 𝓝 q,
      Set.InjOn (WeakMTW.activeProjection y h s) U
 := WeakMTW.activeProjection_critical_local_injective hmtw y h hs
end

end WeakMTWGlobalSupport

end OAI

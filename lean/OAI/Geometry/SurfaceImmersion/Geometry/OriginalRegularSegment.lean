import OAI.Geometry.SurfaceImmersion.Whitney.FiniteRegularPathSmooth
import OAI.Geometry.SurfaceImmersion.Whitney.PathCornerNeighborhood

namespace OAI

/-! Compact unchanged portions of the path between its exceptional
parameters are actual smooth regular embedded arcs. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem original_regular_segment (hi : Function.Injective γ)
    {U : Set ℝ} (hU : IsOpen U) (hU01 : U ⊆ Ioo (0:ℝ) 1)
    (hreg : ∀ t ∈ U, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t))
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ U) :
    ∃ P : SmoothCompactArc planeModel M,
      P.start = a ∧ P.finish = b ∧ P.curve = γ.extend := by
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ.extend U :=
    fun t ht => (hreg t ht).1.contMDiffWithinAt
  have hsub01 : Icc a b ⊆ Icc (0:ℝ) 1 :=
    fun t ht => ⟨(hU01 (hsub ht)).1.le,(hU01 (hsub ht)).2.le⟩
  have hinj : InjOn γ.extend (Icc a b) := (embeddedPath_extend_injOn γ hi).mono hsub01
  exact ⟨⟨γ.extend,a,b,hab,U,hU,hsub,hs,fun t ht => (hreg t ht).2,hinj⟩,rfl,rfl,rfl⟩

theorem original_segment_outside_finite (hi : Function.Injective γ)
    {S : Set ℝ} (hS : S.Finite)
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ S →
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t))
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a < b)
    (havoid : Disjoint (Icc a b) S) :
    ∃ P : SmoothCompactArc planeModel M,
      P.start = a ∧ P.finish = b ∧ P.curve = γ.extend := by
  apply original_regular_segment hi (isOpen_Ioo.sdiff hS.isClosed) sdiff_subset
    (fun t ht => hreg t ht.1 ht.2) hab
  intro t ht
  exact ⟨⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩,fun hs => disjoint_left.mp havoid ht hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

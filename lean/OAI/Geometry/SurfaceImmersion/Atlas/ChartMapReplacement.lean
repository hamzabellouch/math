import OAI.Geometry.SurfaceImmersion.Atlas.ChartPushforward
import OAI.Geometry.SurfaceImmersion.Geometry.GenericProjectionParameter

namespace OAI

/-! A compactly supported change of a coordinate representative produces
an actual global smooth map, retaining its local and exterior germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem chart_map_replacement (p : M) {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {f₀ F : Base → ProjectionTarget 3} (hF : ContDiff ℝ ∞ F) (hf₀ : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport (F-f₀))
    (hs : tsupport (F-f₀) ⊆ (chart p).target)
    {O : Set Base} (hO : IsOpen O)
    (hmatch : EqOn (f ∘ (chart p).symm) f₀ O) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ q ∈ (chart p).source, chart p q ∈ O →
        g =ᶠ[𝓝 q] F ∘ chart p) ∧
      ∀ q ∉ (chart p).symm '' tsupport (F-f₀), g =ᶠ[𝓝 q] f := by
  let δ := F-f₀
  let g := f+chartPushforward p δ
  refine ⟨g,hf.add (chartPushforward_smooth p (hF.sub hf₀) hc hs),?_,?_⟩
  · intro q hq hOq
    filter_upwards [(chart p).open_source.mem_nhds hq,
      ((chart p).continuousAt hq).preimage_mem_nhds (hO.mem_nhds hOq)] with y hy hOy
    have hm := hmatch hOy
    change f ((chart p).symm (chart p y)) = f₀ (chart p y) at hm
    rw [(chart p).left_inv hy] at hm
    change f y+chartPushforward p δ y = F (chart p y)
    rw [chartPushforward_source p δ hy,hm]
    exact add_sub_cancel _ _
  · intro q hq
    have hn : q ∉ tsupport (chartPushforward p δ) :=
      fun h => hq (chartPushforward_tsupport p hc hs h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+chartPushforward p δ y = f y
    rw [hy]
    exact add_zero _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

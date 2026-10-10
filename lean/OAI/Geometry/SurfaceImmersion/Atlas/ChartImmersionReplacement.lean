import OAI.Geometry.SurfaceImmersion.Atlas.ChartPushforward

namespace OAI

/-! Transplanting an actual compactly supported immersion replacement
through a surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem chart_immersion_replacement (p : M) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {f₀ F : Base → V} (hF : ContDiff ℝ ∞ F) (hf₀ : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport (F-f₀))
    (hs : tsupport (F-f₀) ⊆ (chart p).target)
    {O : Set Base} (hO : IsOpen O) (hKO : tsupport (F-f₀) ⊆ O)
    (hmatch : EqOn (f ∘ (chart p).symm) f₀ O)
    (hIF : ∀ x, Function.Injective (fderiv ℝ F x))
    (hIf : ∀ q ∉ (chart p).symm '' tsupport (F-f₀),
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f q)) :
    ∃ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ g ∧
      (∀ q, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g q)) ∧
      ∀ q ∉ (chart p).symm '' tsupport (F-f₀), g q = f q := by
  let δ := F-f₀
  let g := f+chartPushforward p δ
  have hg : ContMDiff planeModel 𝓘(ℝ,V) ∞ g :=
    hf.add (chartPushforward_smooth p (hF.sub hf₀) hc hs)
  refine ⟨g,hg,?_,?_⟩
  · intro q
    by_cases hq : q ∈ (chart p).symm '' tsupport δ
    · obtain ⟨x,hx,rfl⟩ := hq
      have ht := hs hx
      have hsource := (chart p).map_target ht
      have hxo : chart p ((chart p).symm x) ∈ O := by
        rw [(chart p).right_inv ht]
        exact hKO hx
      have he : g =ᶠ[𝓝 ((chart p).symm x)] F ∘ chart p := by
        filter_upwards [(chart p).open_source.mem_nhds hsource,
          ((chart p).continuousAt hsource).preimage_mem_nhds (hO.mem_nhds hxo)] with y hy hOy
        have hm := hmatch hOy
        change f ((chart p).symm (chart p y)) = f₀ (chart p y) at hm
        rw [(chart p).left_inv hy] at hm
        change f y+chartPushforward p δ y = F (chart p y)
        rw [chartPushforward_source p δ hy,hm]
        exact add_sub_cancel _ _
      rw [he.mfderiv_eq]
      have hFc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,V) ∞ F := hF.contMDiff
      rw [mfderiv_comp _ (hFc.mdifferentiable (by simp)).mdifferentiableAt
        ((chart_mdifferentiable p).mdifferentiableAt hsource),mfderiv_eq_fderiv]
      exact (hIF _).comp ((chart_mdifferentiable p).mfderiv_injective hsource)
    · have hn : q ∉ tsupport (chartPushforward p δ) :=
        fun h => hq (chartPushforward_tsupport p hc hs h)
      have he : g =ᶠ[𝓝 q] f := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        change f y+chartPushforward p δ y = f y
        rw [hy]
        exact add_zero _
      rw [he.mfderiv_eq]
      exact hIf q hq
  · intro q hq
    change f q+chartPushforward p δ q = f q
    rw [chartPushforward_zero_off p δ hq,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.CoordinatePushforward

namespace OAI

/-! A supported immersion replacement in constructed smooth surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [T2Space M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinate_immersion_replacement (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {f₀ F : Base → V} (hF : ContDiff ℝ ∞ F) (hf₀ : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport (F-f₀)) (hs : tsupport (F-f₀) ⊆ c.target)
    {O : Set Base} (hO : IsOpen O) (hKO : tsupport (F-f₀) ⊆ O)
    (hmatch : EqOn (f ∘ c.symm) f₀ O)
    (hIF : ∀ x ∈ tsupport (F-f₀), Function.Injective (fderiv ℝ F x))
    (hIf : ∀ q ∉ c.symm '' tsupport (F-f₀),
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f q)) :
    ∃ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ g ∧
      (∀ q, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g q)) ∧
      (∀ q ∉ c.symm '' tsupport (F-f₀), g =ᶠ[𝓝 q] f) ∧
      ∀ q ∈ c.source, c q ∈ O → g =ᶠ[𝓝 q] F ∘ c := by
  let δ := F-f₀
  let g := f+coordinatePushforward c δ
  have hg : ContMDiff planeModel 𝓘(ℝ,V) ∞ g :=
    hf.add (coordinatePushforward_smooth c hcs (hF.sub hf₀) hc hs)
  have hout : ∀ q ∉ c.symm '' tsupport δ, g =ᶠ[𝓝 q] f := by
    intro q hq
    have hn : q ∉ tsupport (coordinatePushforward c δ) :=
      fun h => hq (coordinatePushforward_tsupport c hc hs h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+coordinatePushforward c δ y = f y
    rw [hy]
    exact add_zero _
  have hin : ∀ q ∈ c.source, c q ∈ O → g =ᶠ[𝓝 q] F ∘ c := by
    intro q hq hOq
    filter_upwards [c.open_source.mem_nhds hq,
      (c.continuousAt hq).preimage_mem_nhds (hO.mem_nhds hOq)] with y hy hOy
    have hm := hmatch hOy
    change f (c.symm (c y)) = f₀ (c y) at hm
    rw [c.left_inv hy] at hm
    change f y+coordinatePushforward c δ y = F (c y)
    rw [coordinatePushforward_source c δ hy,hm]
    exact add_sub_cancel _ _
  refine ⟨g,hg,?_,hout,hin⟩
  intro q
  by_cases hq : q ∈ c.symm '' tsupport δ
  · obtain ⟨x,hx,rfl⟩ := hq
    have ht := hs hx
    have hsource := c.map_target ht
    have hcx : c (c.symm x) = x := c.right_inv ht
    have hOcx : c (c.symm x) ∈ O := by rw [hcx]; exact hKO hx
    rw [(hin _ hsource hOcx).mfderiv_eq]
    have hFc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,V) ∞ F := hF.contMDiff
    have hd : c.MDifferentiable planeModel 𝓘(ℝ,Base) :=
      ⟨hcs.mdifferentiableOn (by simp),hci.mdifferentiableOn (by simp)⟩
    rw [mfderiv_comp _ (hFc.mdifferentiable (by simp)).mdifferentiableAt
      (hd.mdifferentiableAt hsource),mfderiv_eq_fderiv,hcx]
    exact (hIF x hx).comp (hd.mfderiv_injective hsource)
  · rw [(hout q hq).mfderiv_eq]
    exact hIf q hq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

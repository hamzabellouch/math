import OAI.Analysis.CircleDomains.Topology.RealInjectiveOpenImage
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Geometry.Manifold.ChartedSpace

namespace OAI

/-! Local real charts turn a continuous injection between curves into
an open map. This supplies the topology of a regular Jordan boundary. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma continuous_injective_local_real_image
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {f : M → N} (hf : Continuous f) (hi : Injective f)
    (c : OpenPartialHomeomorph ℝ M) (d : OpenPartialHomeomorph N ℝ)
    {x : M} (hx : x ∈ c.target) (hfx : f x ∈ d.source)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) : f '' U ∈ 𝓝 (f x) := by
  let V : Set ℝ := c.source ∩ c ⁻¹' (U ∩ f ⁻¹' d.source)
  let g : ℝ → ℝ := fun r => d (f (c r))
  have hV : IsOpen V := c.isOpen_inter_preimage (hU.inter (d.open_source.preimage hf))
  have hcd (r : ℝ) (hr : r ∈ V) : f (c r) ∈ d.source := hr.2.2
  have hg : ContinuousOn g V := d.continuousOn.comp
    (hf.comp_continuousOn (c.continuousOn.mono inter_subset_left)) hcd
  have hgi : InjOn g V := by
    intro r hr s hs he
    exact c.injOn hr.1 hs.1 (hi (d.injOn (hcd r hr) (hcd s hs) he))
  have hG := real_open_image_of_continuousOn_injOn hV hg hgi
  have hGt : g '' V ⊆ d.target := by
    rintro y ⟨r, hr, rfl⟩
    exact d.map_source (hcd r hr)
  have hW : IsOpen (d.symm '' (g '' V)) :=
    d.symm.isOpen_image_of_subset_source hG hGt
  have hcx : c.symm x ∈ V := by
    refine ⟨c.map_target hx, ?_⟩
    change c (c.symm x) ∈ U ∧ f (c (c.symm x)) ∈ d.source
    simpa only [c.right_inv hx] using And.intro hxU hfx
  have hxg : g (c.symm x) = d (f x) := by
    dsimp only [g]
    rw [c.right_inv hx]
  have hxW : f x ∈ d.symm '' (g '' V) :=
    ⟨d (f x), ⟨c.symm x, hcx, hxg⟩, d.left_inv hfx⟩
  apply mem_of_superset (hW.mem_nhds hxW)
  rintro y ⟨s, ⟨r, hr, rfl⟩, rfl⟩
  exact ⟨c r, hr.2.1, (d.left_inv (hcd r hr)).symm⟩

lemma isOpenMap_of_injective_real_manifolds
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℝ M] [ChartedSpace ℝ N]
    {f : M → N} (hf : Continuous f) (hi : Injective f) : IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  exact continuous_injective_local_real_image hf hi (chartAt ℝ x).symm
    (chartAt ℝ (f x)) (mem_chart_source ℝ x) (mem_chart_source ℝ (f x)) hU hx

end CircleDomainRigidity

end

end OAI

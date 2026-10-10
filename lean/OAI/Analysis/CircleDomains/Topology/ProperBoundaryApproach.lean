import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! A homeomorphism between open subsets of compact ambient spaces is
proper at the omitted boundary. The conclusion concerns the whole target
frontier and does not presuppose a pointwise boundary extension. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma tendsto_frontier_of_inverse {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    {U : Set X} {V : Set Y} {f : X → Y} {fi : Y → X} {p : X}
    (hV : IsOpen V) (hm : MapsTo f U V) (him : MapsTo fi V U)
    (hic : ContinuousOn fi V) (hl : ∀x∈U,fi (f x)=x) (hp : p∉U) :
    Tendsto f (𝓝[U] p) (𝓝ˢ (frontier V)) := by
  apply Filter.tendsto_def.mpr
  intro A hA
  obtain ⟨O,hO,hFO,hOA⟩ := mem_nhdsSet_iff_exists.mp hA
  let K := closure V ∩ Oᶜ
  have hKc : IsCompact K := (isClosed_closure.inter hO.isClosed_compl).isCompact
  have hKV : K⊆V := by
    intro y hy
    by_contra hyV
    have hyF : y∈frontier V := by
      rw [frontier, hV.interior_eq]
      exact ⟨hy.1,hyV⟩
    exact hy.2 (hFO hyF)
  have hIc : IsCompact (fi '' K) := hKc.image_of_continuousOn (hic.mono hKV)
  have hpI : p∉fi '' K := by
    rintro ⟨y,hy,rfl⟩
    exact hp (him (hKV hy))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hIc.isClosed.isOpen_compl.mem_nhds hpI)] with x hx hxI
  apply hOA
  by_contra hfx
  apply hxI
  refine ⟨f x,⟨subset_closure (hm hx),hfx⟩,hl x hx⟩

lemma tendsto_of_constant_on_set {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {S : Set X} {g : X → Y} {b : Y}
    (hc : ∀x∈S,ContinuousAt g x) (he : ∀x∈S,g x=b) :
    Tendsto g (𝓝ˢ S) (𝓝 b) := by
  apply Filter.tendsto_def.mpr
  intro A hA
  apply mem_nhdsSet_iff_forall.mpr
  intro x hx
  have ht := (hc x hx).tendsto
  rw [he x hx] at ht
  exact ht hA

lemma tendsto_boundary_value_of_inverse {X Y Z : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [TopologicalSpace Z]
    {U : Set X} {V : Set Y} {f : X → Y} {fi : Y → X} {p : X}
    {g : Y → Z} {b : Z}
    (hV : IsOpen V) (hm : MapsTo f U V) (him : MapsTo fi V U)
    (hic : ContinuousOn fi V) (hl : ∀x∈U,fi (f x)=x) (hp : p∉U)
    (hgc : ∀y∈frontier V,ContinuousAt g y) (hgb : ∀y∈frontier V,g y=b) :
    Tendsto (g ∘ f) (𝓝[U] p) (𝓝 b) :=
  (tendsto_of_constant_on_set hgc hgb).comp
    (tendsto_frontier_of_inverse hV hm him hic hl hp)

end CircleDomainRigidity

end

end OAI

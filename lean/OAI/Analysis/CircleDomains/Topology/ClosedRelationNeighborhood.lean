import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! A closed relation with compact target sends a neighborhood of a
compact source set into every open neighborhood of its fibers. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_relation_neighborhood {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {R : X → Y → Prop}
    (hR : IsClosed {p : X × Y | R p.1 p.2}) {K : Set X} {U : Set Y}
    (hU : IsOpen U) (hKU : ∀ x ∈ K, ∀ y, R x y → y ∈ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∀ y, R x y → y ∈ U := by
  let B := {p : X × Y | R p.1 p.2} ∩ (univ ×ˢ Uᶜ)
  have hB : IsClosed B := hR.inter (isClosed_univ.prod hU.isClosed_compl)
  have hproj : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  refine ⟨(Prod.fst '' B)ᶜ,hproj.isOpen_compl,?_,?_⟩
  · intro x hx
    rintro ⟨p,hp,hpx⟩
    have hr : R p.1 p.2 := hp.1
    have hr' : R x p.2 := by simpa only [hpx] using hr
    exact hp.2.2 (hKU x hx p.2 hr')
  · intro x hx y hxy
    by_contra hy
    exact hx ⟨(x,y),⟨hxy,⟨mem_univ _,hy⟩⟩,rfl⟩

 theorem closed_relation_selection_continuousAt {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    (b : X → Y) (hb : ∀ x, R x (b x)) {x : X}
    (hfiber : ∀ y, R x y → y = b x) : ContinuousAt b x := by
  apply continuousAt_def.mpr
  intro U hU
  obtain ⟨W,hWU,hW,hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨V,hV,hxV,hmap⟩ := closed_relation_neighborhood (K := {x}) hR hW (by
    intro z hz y hzy
    rw [mem_singleton_iff] at hz
    subst z
    rwa [hfiber y hzy])
  filter_upwards [hV.mem_nhds (hxV (mem_singleton x))] with z hz
  exact hWU (hmap z hz (b z) (hb z))

end CircleDomainRigidity

end

end OAI

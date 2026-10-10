import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! Closed equivalence relations on compact Hausdorff spaces have closed
quotient maps and Hausdorff quotient spaces. These elementary topological
bridges precede the sphere realization in the Moore application. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma quotientMk_isClosedMap_of_closed_relation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    IsClosedMap (Quotient.mk' : X → Quotient r) := by
  intro C hC
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have hs : IsClosed {p : X × X | r p.1 p.2 ∧ p.2 ∈ C} :=
    hr.inter (hC.preimage continuous_snd)
  have hi := continuous_fst.isClosedMap _ hs
  convert hi using 1
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨(x,y), ⟨r.symm (Quotient.exact he), hy⟩, rfl⟩
  · rintro ⟨⟨a,b⟩, ⟨hab,hb⟩, rfl⟩
    exact ⟨b, hb, Quotient.sound (r.symm hab)⟩

lemma quotientMk_fiber_isClosed_of_closed_relation
    {X : Type*} [TopologicalSpace X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2})
    (a : Quotient r) : IsClosed ((Quotient.mk' : X → Quotient r) ⁻¹' {a}) := by
  induction a using Quotient.inductionOn with
  | h x =>
    convert hr.preimage (continuous_id.prodMk (continuous_const (y := x))) using 1
    ext y
    change (Quotient.mk' y = Quotient.mk' x) ↔ r y x
    exact Quotient.eq'

lemma quotient_t2Space_of_closed_relation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    T2Space (Quotient r) := by
  let q : X → Quotient r := Quotient.mk'
  have hq : IsClosedMap q := quotientMk_isClosedMap_of_closed_relation r hr
  refine ⟨fun a b hab => ?_⟩
  have hd : Disjoint (q ⁻¹' {a}) (q ⁻¹' {b}) := by
    apply Set.disjoint_left.mpr
    intro x ha hb
    exact hab (ha.symm.trans hb)
  obtain ⟨U,V,hU,hV,haU,hbV,hUV⟩ := normal_separation
    (quotientMk_fiber_isClosed_of_closed_relation r hr a)
    (quotientMk_fiber_isClosed_of_closed_relation r hr b) hd
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ, (hq _ hU.isClosed_compl).isOpen_compl,
    (hq _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨x,hx,he⟩
    exact hx (haU he)
  · rintro ⟨x,hx,he⟩
    exact hx (hbV he)
  · apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨x,rfl⟩ := Quotient.mk'_surjective z
    have hxU : x ∈ U := by
      by_contra hx
      exact hzU ⟨x,hx,rfl⟩
    have hxV : x ∈ V := by
      by_contra hx
      exact hzV ⟨x,hx,rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV

end CircleDomainRigidity

end

end OAI

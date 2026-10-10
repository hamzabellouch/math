import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace CompactContinuation
variable {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

 theorem fiber_tube {F : P × X → Y} (hF : Continuous F) {s : P} {y : Y}
    {U : Set X} (hU : IsOpen U) (hu : ∀ x, F (s,x) = y → x ∈ U) :
    ∃ J ∈ 𝓝 s, ∃ W ∈ 𝓝 y, ∀ t ∈ J, ∀ x, F (t,x) ∈ W → x ∈ U := by
  let N : Set ((P × Y) × X) := {q | q.2 ∈ U ∨ F (q.1.1,q.2) ≠ q.1.2}
  have hN : IsOpen N := (hU.preimage continuous_snd).union
    (isClosed_eq (hF.comp (continuous_fst.fst.prodMk continuous_snd)) continuous_fst.snd).isOpen_compl
  have hsub : ({(s,y)} : Set (P × Y)) ×ˢ (univ : Set X) ⊆ N := by
    rintro ⟨⟨t,z⟩,x⟩ ⟨he,hx⟩
    have he' : (t,z) = (s,y) := he
    cases he'
    change x ∈ U ∨ F (s,x) ≠ y
    by_cases hx : F (s,x) = y
    · exact Or.inl (hu x hx)
    · exact Or.inr hx
  obtain ⟨A,B,hA,hB,hsA,hXB,hAB⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ hN hsub
  obtain ⟨J,hJ,W,hW,hJW⟩ := mem_nhds_prod_iff.mp
    (hA.mem_nhds (hsA (mem_singleton (s,y))))
  refine ⟨J,hJ,W,hW,?_⟩
  intro t ht x hx
  have hh : x ∈ U ∨ F (t,x) ≠ F (t,x) :=
    @hAB ((t,F (t,x)),x) ⟨hJW ⟨ht,hx⟩,hXB (mem_univ x)⟩
  exact hh.resolve_right (not_ne_iff.mpr rfl)

 theorem limit_injective [T2Space X] [LocallyConnectedSpace Y]
    {F : P × X → Y} (hF : Continuous F) {s : P} {sⱼ : ℕ → P}
    (hs : Tendsto sⱼ atTop (𝓝 s))
    (hbij : ∀ j, Function.Bijective (fun x => F (sⱼ j,x)))
    (hloc : ∀ x : X, ∃ N ∈ 𝓝 x, InjOn (fun z => F (s,z)) N) :
    Function.Injective (fun x => F (s,x)) := by
  intro p q hpq
  change F (s,p) = F (s,q) at hpq
  by_contra hne
  obtain ⟨N,hN,hNI⟩ := hloc p
  obtain ⟨U,⟨hpU,hU⟩,hUN⟩ := (hasBasis_opens_closure p).mem_iff.mp hN
  let V : Set X := (closure U)ᶜ
  have hpN : p ∈ N := hUN (subset_closure hpU)
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hqV : q ∈ V := by
    intro hq
    exact hne (hNI hpN (hUN hq) hpq)
  have hcover : ∀ x, F (s,x) = F (s,p) → x ∈ U ∪ V := by
    intro x hx
    by_cases hxc : x ∈ closure U
    · have he : x = p := hNI (hUN hxc) hpN hx
      exact Or.inl (he.symm ▸ hpU)
    · exact Or.inr hxc
  obtain ⟨J,hJ,W,hW,hcover'⟩ := fiber_tube hF (hU.union hV) hcover
  obtain ⟨A,⟨hA,hpA,hAc⟩,hAW⟩ := (LocallyConnectedSpace.open_connected_basis (F (s,p))).mem_iff.mp hW
  have hpLim : Tendsto (fun j => F (sⱼ j,p)) atTop (𝓝 (F (s,p))) :=
    hF.continuousAt.tendsto.comp (hs.prodMk_nhds tendsto_const_nhds)
  have hqLim : Tendsto (fun j => F (sⱼ j,q)) atTop (𝓝 (F (s,p))) := by
    rw [hpq]
    exact hF.continuousAt.tendsto.comp (hs.prodMk_nhds tendsto_const_nhds)
  have hjT : ∀ᶠ j in atTop, sⱼ j ∈ J := hs hJ
  obtain ⟨j,⟨hjJ,hjp⟩,hjq⟩ := ((hjT.and (hpLim (hA.mem_nhds hpA))).and
    (hqLim (hA.mem_nhds hpA))).exists
  let f : X → Y := fun x => F (sⱼ j,x)
  have hf : Continuous f := hF.comp (continuous_const.prodMk continuous_id)
  let e : X ≃ₜ Y := (Equiv.ofBijective f (hbij j)).toHomeomorphOfContinuousClosed hf hf.isClosedMap
  have hc : IsPreconnected (f ⁻¹' A) := e.isPreconnected_preimage.mpr hAc.isPreconnected
  have hd : (f ⁻¹' A) ⊆ U ∪ V := fun x hx => hcover' _ hjJ x (hAW hx)
  have hdisc : Disjoint U V := disjoint_compl_right_iff_subset.mpr subset_closure
  have hh := hc U V hU hV hd ⟨p,hjp,hpU⟩ ⟨q,hjq,hqV⟩
  obtain ⟨x,hx,hxu,hxv⟩ := hh
  exact Set.disjoint_left.mp hdisc hxu hxv

end CompactContinuation
end

end WeakMTWGlobalSupport

end OAI

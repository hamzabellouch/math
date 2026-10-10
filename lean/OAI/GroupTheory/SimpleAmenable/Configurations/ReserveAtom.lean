import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AtomConjugation

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ReserveAtomSupport

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def subtypeAlternatingHom (S : Finset I) :
    alternatingGroup S →* alternatingGroup I :=
  { toFun := fun g => ⟨Equiv.Perm.ofSubtype g.val, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact g.property⟩
    map_one' := Subtype.ext (map_one Equiv.Perm.ofSubtype)
    map_mul' := fun x y => Subtype.ext (map_mul Equiv.Perm.ofSubtype x.val y.val) }

theorem swapLabel_subtype (S : Finset I) (a : SwapLabel I) (ha : a.val.support ⊆ S) :
    ∃ b : SwapLabel S, Equiv.Perm.ofSubtype b.val = a.val := by
  obtain ⟨i,j,hij,heq⟩ := a.property
  have hi : i ∈ S := ha (by rw [heq, Equiv.Perm.support_swap hij]; simp)
  have hj : j ∈ S := ha (by rw [heq, Equiv.Perm.support_swap hij]; simp)
  let b : SwapLabel S := ⟨Equiv.swap ⟨i,hi⟩ ⟨j,hj⟩,
    ⟨i,hi⟩,⟨j,hj⟩,fun h => hij (congrArg Subtype.val h), rfl⟩
  exact ⟨b,by simp only [b, Equiv.Perm.ofSubtype_swap_eq,heq]⟩

theorem supported_reserveAtoms_generate (S : Finset I) (a : SwapLabel I)
    (ha : a.val.support ⊆ S) (g : alternatingGroup I) (hg : g.val.support ⊆ S) :
    g ∈ Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t} := by
  classical
  let K := Subgroup.closure {h : alternatingGroup I | ∃ t : SwapLabel I,
      t.val.support ⊆ S ∧ h = reserveAtom a t}
  obtain ⟨aS,haS⟩ := swapLabel_subtype S a ha
  obtain ⟨gS,hgS⟩ := Equiv.Perm.mem_range_ofSubtype_iff.mpr hg
  have hgS' : gS ∈ alternatingGroup S := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hgS]
    exact g.property
  have hle : Subgroup.closure (Set.range (reserveAtom aS)) ≤
      K.comap (subtypeAlternatingHom S) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    let t' : SwapLabel I := ⟨Equiv.Perm.ofSubtype t.val,t.property.of_subtype_isSwap⟩
    apply Subgroup.subset_closure
    refine ⟨t',?_,?_⟩
    · exact Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨t.val,rfl⟩
    · apply Subtype.ext
      change Equiv.Perm.ofSubtype (aS.val * t.val) = a.val * Equiv.Perm.ofSubtype t.val
      rw [map_mul,haS]
  have hm := hle (reserveAtoms_generate aS ▸
    Subgroup.mem_top (⟨gS,hgS'⟩ : alternatingGroup S))
  change subtypeAlternatingHom S ⟨gS,hgS'⟩ ∈ K at hm
  have heq : subtypeAlternatingHom S ⟨gS,hgS'⟩ = g := Subtype.ext hgS
  rwa [heq] at hm

end ReserveAtomSupport

end SimpleAmenable
end
end

end OAI

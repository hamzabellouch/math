import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OperationalControl
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullAlphabetGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallControlCalculus
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

abbrev ControlAlphabet (α : Type*) [Fintype α] [DecidableEq α] :=
  {I : Finset α // 5 ≤ I.card ∧ I.card ≤ 10}

instance controlAlphabet_perfect (I : ControlAlphabet α) :
    Group.IsPerfect (alternatingGroup I.val) := alphabetPerfect I.val I.property.1

abbrev TrackStar (α : Type*) [Fintype α] [DecidableEq α] :=
  UniversalExtension (alternatingGroup α)

def SmallSupported (L : Finset α → Subgroup H) (f : TrackStar α →* H) : Prop :=
  ∀ I : ControlAlphabet α, (f.comp (universalMap (subtypeAlternatingHom I.val))).range ≤ L I.val

def SmallControlled (c : alternatingGroup α →* H) (f g : TrackStar α →* H) : Prop :=
  ∀ I : ControlAlphabet α,
    SameActionOn (g.comp (universalMap (subtypeAlternatingHom I.val)))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range

omit [Fintype α] [DecidableEq α] [Group.IsPerfect (alternatingGroup α)] in
theorem five_bank_of_card (I : Finset α) (hI : I.card = 5) :
    ∃ s : Fin 5 ↪ α, Finset.univ.map s = I := by
  classical
  let e : Fin 5 ≃ I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let s := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ I))
  refine ⟨s,?_⟩
  ext x
  constructor
  · rintro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact (e i).property
  · intro hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩

omit [Group.IsPerfect (alternatingGroup α)] in

theorem small_star_representative (hα : 10 ≤ Fintype.card α)
    (σ : alternatingGroup α) (hσ : σ.val.support.card ≤ 10) :
    ∃ (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)),
      subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) t) = σ := by
  obtain ⟨I,hSI,_,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ σ.val.support) hσ (by simpa using hα)
  let J : ControlAlphabet α := ⟨I,by omega,by omega⟩
  obtain ⟨s,hs⟩ := (subtypeAlternatingHom_mem_range I σ).mpr hSI
  let := alphabetPerfect I (by omega)
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup J.val) s
  exact ⟨J,t,by simpa only [ht] using hs⟩

theorem small_control_transfer (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (f g : TrackStar α →* H) (hf : SmallSupported L f) (hfg : SmallControlled c f g)
    (J : Finset α) (u : H) (hu : u ∈ L J) (hreserve : J.card+10 ≤ Fintype.card α)
    (hug : ∀ (I : ControlAlphabet α) t, Commute u (g (universalMap (subtypeAlternatingHom I.val) t))) :
    ∀ x ∈ f.range, Commute u x := by
  classical
  let C := Subgroup.centralizer ({u} : Set H)
  have hC : f.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩
    let A : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,by have hh := I.property.2; omega⟩
    have hx : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L I.val :=
      hf A ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := five_bank_of_card I.val I.property.2
    have hx' : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L (Finset.univ.map s) := by
      rwa [hs]
    have hres : (J ∪ Finset.univ.map s).card + 5 ≤ Fintype.card α := by
      rw [hs]
      have hh := Finset.card_union_le J I.val
      rw [I.property.2] at hh
      omega
    have hh := fresh_bank_conditional_control L c hc hd s J u
      (f (universalMap (subtypeAlternatingHom I.val) t)) hu hx' hres ?_
    · intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hh.eq
    · intro σ hσ
      obtain ⟨K,v,hv⟩ := small_star_representative (by omega : 10 ≤ Fintype.card α) σ hσ
      refine ⟨g (universalMap (subtypeAlternatingHom K.val) v),hug K v,?_⟩
      have hh := hfg K v _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩
      have he := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom K.val)) v
      change universalProjection (alternatingGroup α) (universalMap (subtypeAlternatingHom K.val) v) = _ at he
      simpa only [MonoidHom.comp_apply,he,hv] using hh
  intro x hx
  exact hC hx u (Set.mem_singleton u)

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI

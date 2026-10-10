import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.LocalAtomComparison
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallFamilyWords

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallFamilyGlobal

variable {D H Q T : Type*} [Group D] [Group H] [Group Q] [Group T]

theorem centralOn_range_iff_hasCentralLaw (q : H →* Q) (e : D →* H)
    (v : D →* T) (ρ : T →* Q) (hρ : Function.Injective ρ)
    (he : q.comp e = ρ.comp v) :
    CentralOn q e.range ↔ HasCentralLaw v e.rangeRestrict := by
  have hk (w : D) : q (e w) = 1 ↔ v w = 1 := by
    have hh := DFunLike.congr_fun he w
    change q (e w) = ρ (v w) at hh
    rw [hh,← map_one ρ]
    exact hρ.eq_iff
  rw [hasCentralLaw_iff]
  constructor
  · intro h w hw
    exact h ((hk w).mpr hw)
  · intro h x hx
    obtain ⟨w,hw⟩ := x.property
    have hx' : q (e w) = 1 := by
      change q x.val = 1 at hx
      simpa only [hw] using hx
    have ht := h w ((hk w).mp hx')
    have heq : e.rangeRestrict w = x := Subtype.ext hw
    rwa [heq] at ht

variable {α ι Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω]

theorem smallFamily_centralOn
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (q : H →* Q) (ρ : (Ω → alternatingGroup α) →* Q) (hρ : Function.Injective ρ)
    (hproj : ∀ I i, q.comp (F I i) =
      ρ.comp ((maskFamily U i).comp (subtypeAlternatingHom I.val)))
    (K : Finset α → Subgroup H)
    (hlaw : ∀ S, S.card ≤ 15 → CentralOn q (K S))
    (hcontain : ∀ S, S.card ≤ 15 → ∀ I, I.val ⊆ S → ∀ i, (F I i).range ≤ K S)
    (hα : 5 ≤ Fintype.card α) : CentralOn q (smallFamilyEval F).range := by
  classical
  let e := smallFamilyEval F
  let v := smallFamilyModel (α := α) U
  have he : q.comp e = ρ.comp v := by
    apply FreeGroup.ext_hom
    rintro ⟨I,i,s⟩
    simpa only [e,v,MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of] using
      DFunLike.congr_fun (hproj I i) s
  apply (centralOn_range_iff_hasCentralLaw q e v ρ hρ he).mpr
  let : Group.IsPerfect e.range := smallFamilyEval_perfect F
  obtain ⟨E,_hEsub,hE⟩ := Finset.exists_subset_card_eq (show 5 ≤ (Finset.univ : Finset α).card by simpa using hα)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_ne (show 1 < E.card by omega) x
  let a : SwapLabel α := ⟨Equiv.swap x y,x,y,Ne.symm hyx,rfl⟩
  have ha : a.val.support ⊆ E := by
    change (Equiv.swap x y).support ⊆ E
    rw [Equiv.Perm.support_swap (Ne.symm hyx)]
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  refine small_support_assignment_law (smallFamilyLocal (ι := ι)) smallFamilyLocal_mono
    v e.rangeRestrict e.rangeRestrict_surjective smallFamilyLocal_generate
    (smallFamilyModel_support U) ?_ E hE a ha ?_
  · intro S hS d hd hv z hz
    apply Commute.of_map (f := e.range.subtype) Subtype.val_injective
    have hle := smallFamilyLocal_map_le F S (K S) (hcontain S hS)
    apply (centralOn_iff q (K S)).mp (hlaw S hS) (e d) (hle ⟨d,hd,rfl⟩)
    · have hh := DFunLike.congr_fun he d
      change q (e d) = ρ (v d) at hh
      rw [hh,hv,map_one]
    · exact hle ⟨z,hz,rfl⟩
  · intro S hS _ g hg
    exact smallFamilyModel_complete U hsep S hS g hg

end SmallFamilyGlobal

section GlobalPrimitiveTable

theorem exists_alphabet_balance {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : S.card < Fintype.card α) : ∃ b, b ∉ S := by
  classical
  by_contra h
  push Not at h
  have he : S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [he,Finset.card_univ] at hS
  exact (lt_irrefl _ hS)

noncomputable def smallAlphabetBalance {m : ℕ} (hlarge : 15 < m+1)
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15) : Fin (m+1) :=
  (exists_alphabet_balance S (by simpa using lt_of_le_of_lt hS hlarge)).choose

theorem smallAlphabetBalance_notMem {m : ℕ} (hlarge : 15 < m+1)
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15) :
    smallAlphabetBalance hlarge S hS ∉ S :=
  (exists_alphabet_balance S (by simpa using lt_of_le_of_lt hS hlarge)).choose_spec

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

noncomputable def smallPrimitiveInputs (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (I : FiveAlphabet (Fin (m+1))) :
    Option ι → alternatingGroup I.val →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.primitiveFamily I.val (smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega))
    (smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)) P

noncomputable def smallPrimitiveCarrier (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (S : Finset (Fin (m+1))) :
    Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)) :=
  if hS : S.card ≤ 15 then
    (copyFamilyEval (B.primitiveFamily S (smallAlphabetBalance hlarge S hS)
      (smallAlphabetBalance_notMem hlarge S hS) P)).range
  else ⊥

theorem smallPrimitiveInputs_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (I : FiveAlphabet (Fin (m+1))) (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.smallPrimitiveInputs hlarge P I i) =
    (actualPolygonTableHom (primitiveTests (a := a) (r := r) P)).comp
      ((maskFamily (actualTestMask (primitiveTests (a := a) (r := r) P)) i).comp
        (subtypeAlternatingHom I.val)) := by
  rw [smallPrimitiveInputs,B.primitiveFamily_projection]
  have he := actualAlphabetTableHom_masks I.val (primitiveTests (a := a) (r := r) P) i
  change ((actualPolygonTableHom _).comp (alphabetAssignment I.val)).comp _ = _ at he
  rw [MonoidHom.comp_assoc,alphabetAssignment_mask] at he
  exact he.symm

omit [Finite ι] in
theorem smallPrimitiveInputs_local (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
    (I : FiveAlphabet (Fin (m+1))) (hIS : I.val ⊆ S) (i : Option ι) :
    (B.smallPrimitiveInputs hlarge P I i).range ≤ B.smallPrimitiveCarrier hlarge P S := by
  rw [smallPrimitiveCarrier,dite_eq_left hS]
  rintro x ⟨s,rfl⟩
  rw [copyFamilyEval_range]
  apply le_iSup (fun j => (B.primitiveFamily S (smallAlphabetBalance hlarge S hS)
    (smallAlphabetBalance_notMem hlarge S hS) P j).range) i
  refine ⟨subalphabetHom hIS s,?_⟩
  exact DFunLike.congr_fun (B.primitiveFamily_inclusion hIS _ _ _ _ P i) s

theorem fullPrimitiveFamily_central (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  apply smallFamily_centralOn (actualTestMask (primitiveTests (a := a) (r := r) P))
    (actualTestMask_separates _) (B.smallPrimitiveInputs hlarge P) _
    (actualPolygonTableHom _) (actualPolygonTableHom_injective _)
    (B.smallPrimitiveInputs_projection hlarge P) (B.smallPrimitiveCarrier hlarge P) ?_
    (B.smallPrimitiveInputs_local hlarge P) (by simpa using (by omega : 5 ≤ m+1))
  intro S hS
  rw [smallPrimitiveCarrier,dite_eq_left hS]
  exact h S hS _ _

end InitialCoverSystem
end GlobalPrimitiveTable

end SimpleAmenable
end
end

end OAI

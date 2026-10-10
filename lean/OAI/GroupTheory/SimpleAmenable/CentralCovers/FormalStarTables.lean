import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairLawAssembly
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSector
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CentralRangeReflection

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalStarTables
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem star_small_range_eq (hα : 5 ≤ Fintype.card α)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val))) :
    (copyFamilyEval F).range=(smallFamilyEval f).range := by
  rw [copyFamilyEval_range,smallFamilyEval_range,iSup_comm]
  apply iSup_congr
  intro i
  rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate hα,Subgroup.map_iSup]
  apply iSup_congr
  intro I
  rw [← MonoidHom.range_comp,hspec]
  apply le_antisymm (range_comp_subset _ _)
  rintro x ⟨s,rfl⟩
  obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
  exact ⟨t,rfl⟩

structure FormalStarTable (F : Option ι → TrackStar α →* H) where
  carrier : Subgroup H
  carrier_eq : carrier=(copyFamilyEval F).range
  input : Option ι → TrackStar α →* carrier
  inclusion : ∀ i, carrier.subtype.comp (input i)=F i
  model : ((ι → Bool) → alternatingGroup α) →* carrier ⧸ Subgroup.center carrier
  onto : Function.Surjective model
  spec : ∀ i, model.comp ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp
      (universalProjection (alternatingGroup α))) =
    (QuotientGroup.mk' _).comp (input i)

theorem formalStarTable_of_small [Finite ι] (hα : 5 ≤ Fintype.card α)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (hlaw : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict) : Nonempty (FormalStarTable F) := by
  classical
  let K := (smallFamilyEval f).range
  have hmem : ∀ i s, F i s ∈ K := by
    intro i s
    change F i s ∈ (smallFamilyEval f).range
    rw [← star_small_range_eq hα F f hspec]
    exact ⟨FreeGroup.of (i,s),copyFamilyEval_of F i s⟩
  let F' : Option ι → TrackStar α →* K := fun i => (F i).codRestrict K (hmem i)
  have hsep : ∀ σ τ : ι → Bool,
      (∀ i, σ ∈ {σ : ι → Bool | σ i=true} ↔ τ ∈ {σ : ι → Bool | σ i=true}) → σ=τ := by
    intro σ τ he
    funext i
    exact Bool.eq_iff_iff.mpr (he i)
  obtain ⟨φ,hφ⟩ := (hasCentralLaw_iff_modelMap _ _ (smallFamilyModel_surjective _ hsep hα)).mp hlaw
  refine ⟨⟨K,(star_small_range_eq hα F f hspec).symm,F',(fun _ => rfl),φ,centralLaw_modelMap_surjective _ _
    (smallFamilyEval f).rangeRestrict_surjective φ hφ,?_⟩⟩
  intro i
  apply universal_five_alphabet_hom_ext hα
  intro I
  ext s
  have hp := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
  have he : F' i (universalMap (subtypeAlternatingHom I.val) s)=
      (smallFamilyEval f).rangeRestrict (FreeGroup.of ⟨I,i,universalProjection _ s⟩) := by
    apply Subtype.ext
    change F i (universalMap (subtypeAlternatingHom I.val) s)=
      smallFamilyEval f (FreeGroup.of ⟨I,i,universalProjection _ s⟩)
    rw [smallFamilyEval_of]
    exact DFunLike.congr_fun (hspec I i) s
  simp only [MonoidHom.comp_apply,he]
  have hh := DFunLike.congr_fun hφ (FreeGroup.of ⟨I,i,universalProjection _ s⟩)
  simp only [MonoidHom.comp_apply] at hp hh
  rw [hp]
  exact hh

namespace FormalStarTable
variable {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)
noncomputable def sector (U : Set (ι → Bool)) : TrackStar α →* H :=
  T.carrier.subtype.comp (centralSector T.model U)

theorem sector_input (i : Option ι) :
    T.sector (match i with | none => Set.univ | some i => {σ | σ i=true})=F i := by
  rw [← T.inclusion i]
  apply congrArg (T.carrier.subtype.comp)
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center T.carrier))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply,centralSector_spec]
  cases i with
  | none => simpa only [MonoidHom.comp_apply,maskFamily] using DFunLike.congr_fun (T.spec none) s
  | some i => simpa only [MonoidHom.comp_apply,maskFamily] using DFunLike.congr_fun (T.spec (some i)) s

theorem sector_mem (U : Set (ι → Bool)) (s : TrackStar α) :
    T.sector U s ∈ (copyFamilyEval F).range := by
  rw [← T.carrier_eq]
  exact (centralSector T.model U s).property

theorem sector_union {U V : Set (ι → Bool)} (hd : Disjoint U V) (s : TrackStar α) :
    T.sector (U ∪ V) s=T.sector U s*T.sector V s := by
  change (centralSector T.model (U ∪ V) s).val=_
  rw [centralSector_union T.model hd]
  rfl

theorem sector_commute {U V : Set (ι → Bool)} (hd : Disjoint U V) (s t : TrackStar α) :
    Commute (T.sector U s) (T.sector V t) := (centralSector_commute T.model hd s t).map T.carrier.subtype

theorem sector_control {U V : Set (ι → Bool)} (hUV : U ⊆ V) :
    SameActionOn (T.sector V) (F none) (T.sector U).range := by
  rw [← T.sector_input none]
  rintro s x ⟨t,rfl⟩
  exact congrArg Subtype.val (centralSector_control T.model hUV s _ ⟨t,rfl⟩)

theorem sector_supported [Finite ι] (L : Finset α → Subgroup H)
    (hF : ∀ i, SmallSupported L (F i)) (U : Set (ι → Bool)) :
    SmallSupported L (T.sector U) := by
  classical
  intro I
  let K := (L I.val).comap T.carrier.subtype
  have hsep : ∀ σ τ : ι → Bool,
      (∀ i, σ ∈ {σ : ι → Bool | σ i=true} ↔ τ ∈ {σ : ι → Bool | σ i=true}) → σ=τ := by
    intro σ τ he
    funext i
    exact Bool.eq_iff_iff.mpr (he i)
  have hm (i : Option ι) (s : alternatingGroup I.val) :
      T.model (maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i (subtypeAlternatingHom I.val s)) ∈
        K.map (QuotientGroup.mk' _) := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
    have hπ := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) t
    have hs := DFunLike.congr_fun (T.spec i) (universalMap (subtypeAlternatingHom I.val) t)
    simp only [MonoidHom.comp_apply] at hπ hs
    rw [hπ] at hs
    rw [hs]
    apply Subgroup.mem_map.mpr
    refine ⟨T.input i (universalMap (subtypeAlternatingHom I.val) t),?_,rfl⟩
    change T.carrier.subtype (T.input i (universalMap (subtypeAlternatingHom I.val) t)) ∈ L I.val
    rw [← MonoidHom.comp_apply,T.inclusion]
    exact hF i I ⟨t,rfl⟩
  have hh := centralSector_supported T.model (fun j : ι => {σ : ι → Bool | σ j=true})
    hsep (subtypeAlternatingHom I.val) K (hm none) (fun i => hm (some i)) U
  rintro x ⟨s,rfl⟩
  exact hh ⟨s,rfl⟩

end FormalStarTable
end FormalStarTables

end SimpleAmenable
end
end

end OAI

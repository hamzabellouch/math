import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairControl
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalStarTables

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalSectorSubfamily
namespace FormalStarTable
variable {α ι κ H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]
    {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

omit [Group.IsPerfect (alternatingGroup α)] in
theorem input_eval : T.carrier.subtype.comp (copyFamilyEval T.input)=copyFamilyEval F := by
  rw [← copyFamilyEval_comp]
  congr 1
  funext i
  exact T.inclusion i

omit [Group.IsPerfect (alternatingGroup α)] in
theorem input_surjective : Function.Surjective (copyFamilyEval T.input) := by
  intro x
  have hx : x.val ∈ (copyFamilyEval F).range := by rw [← T.carrier_eq]; exact x.property
  obtain ⟨w,hw⟩ := hx
  refine ⟨w,Subtype.ext ?_⟩
  have he := DFunLike.congr_fun T.input_eval w
  exact he.trans hw

omit [Group.IsPerfect (alternatingGroup α)] in
theorem model_eval : T.model.comp (formalAssignmentEval (universalProjection (alternatingGroup α)))=
    (QuotientGroup.mk' _).comp (copyFamilyEval T.input) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  have hh := DFunLike.congr_fun (T.spec i) s
  simpa only [MonoidHom.comp_apply,formalAssignmentEval,copySourceMap,FreeGroup.map.of,
    assignmentEval,copyFamilyEval_of] using hh

theorem sector_subfamily_range [Finite κ] (v : κ → ι) (V : Set (κ → Bool)) :
    (T.sector ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V)).range ≤
      (copyFamilyEval (fun i : Option κ => F (i.map v))).range := by
  classical
  let K := ((copyFamilyEval (fun i : Option κ => F (i.map v))).range).comap T.carrier.subtype
  let q := QuotientGroup.mk' (Subgroup.center T.carrier)
  let J := (K.map q).comap (T.model.comp (assignmentPullback (fun σ : ι → Bool => σ ∘ v)))
  have hm (i : Option κ) (s : alternatingGroup α) :
      maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i s ∈ J := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup α) s
    change T.model (assignmentPullback (fun σ : ι → Bool => σ ∘ v)
      (maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i (universalProjection _ t))) ∈ K.map q
    have he : assignmentPullback (fun σ : ι → Bool => σ ∘ v)
        (maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i (universalProjection _ t))=
        maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) (i.map v) (universalProjection _ t) := by
      cases i <;> rfl
    rw [he]
    have hs := DFunLike.congr_fun (T.spec (i.map v)) t
    simp only [MonoidHom.comp_apply] at hs
    rw [hs]
    apply Subgroup.mem_map.mpr
    refine ⟨T.input (i.map v) t,?_,rfl⟩
    change T.carrier.subtype (T.input (i.map v) t) ∈ (copyFamilyEval (fun i : Option κ => F (i.map v))).range
    rw [← MonoidHom.comp_apply,T.inclusion]
    exact ⟨FreeGroup.of (i,t),copyFamilyEval_of _ i t⟩
  have hJ : J=⊤ := assignment_group_generated
    (fun j : κ => {σ : κ → Bool | σ j=true})
    (fun σ τ he => funext (fun i => Bool.eq_iff_iff.mpr (he i))) J (hm none) (fun i => hm (some i))
  have hsec : (centralSector T.model ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V)).range ≤ K := by
    apply perfect_range_le_of_central_image _ q (by rw [QuotientGroup.ker_mk']) K
    rintro x ⟨s,rfl⟩
    change q (centralSector T.model _ s) ∈ K.map q
    rw [centralSector_spec]
    have he : sectorMask ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V) (universalProjection _ s)=
        assignmentPullback (fun σ : ι → Bool => σ ∘ v) (sectorMask V (universalProjection _ s)) := by
      rfl
    rw [he]
    have hh : sectorMask V (universalProjection _ s) ∈ J := by rw [hJ]; trivial
    exact hh
  rintro x ⟨s,rfl⟩
  exact hsec ⟨s,rfl⟩

theorem sector_forward [Finite ι] (γ : T.carrier →* Q) (hγ : Function.Surjective γ)
    (hz : Subgroup.center Q=⊥) (δ : ((ι → Bool) → alternatingGroup α) →* Q)
    (hδ : ∀ i, γ.comp (T.input i)=δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _)))
    (V : Set (ι → Bool)) (s : TrackStar α) :
    γ (centralSector T.model V s)=δ (sectorMask V (universalProjection _ s)) := by
  have hc : Subgroup.center T.carrier ≤ γ.ker := by
    intro x hx
    have hh : γ x ∈ Subgroup.center Q := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨t,rfl⟩ := hγ y
      simpa only [map_mul] using congrArg γ (Subgroup.mem_center_iff.mp hx t)
    simpa only [hz,Subgroup.mem_bot,MonoidHom.mem_ker] using hh
  let γ' := QuotientGroup.lift (Subgroup.center T.carrier) γ hc
  have he : γ'.comp T.model=δ := by
    apply MonoidHom.cancel_right (formalAssignmentEval_surjective
      (universalProjection (alternatingGroup α)) (universalProjection_surjective _)) |>.mp
    rw [MonoidHom.comp_assoc,T.model_eval]
    apply FreeGroup.ext_hom
    rintro ⟨i,t⟩
    have hh := DFunLike.congr_fun (hδ i) t
    simpa only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,γ',QuotientGroup.mk'_apply,QuotientGroup.lift_mk] using hh
  have hh := DFunLike.congr_fun he (sectorMask V (universalProjection _ s))
  change γ' (T.model _)=_ at hh
  rw [← centralSector_spec] at hh
  exact hh

end FormalStarTable
end FormalSectorSubfamily

end SimpleAmenable
end
end

end OAI

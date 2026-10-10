import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConditionalFamilyLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualSectors

variable {P E H Q Ω : Type*} [Group P] [Group E] [Group H] [Group Q]

theorem CentralOn.lift_unique [Group.IsPerfect P] (q : H →* Q) (S : Subgroup H)
    (h : CentralOn q S) (f g : P →* H) (hf : f.range ≤ S) (hg : g.range ≤ S)
    (he : q.comp f = q.comp g) : f = g := by
  let f' : P →* S := f.codRestrict S (fun x => hf ⟨x,rfl⟩)
  let g' : P →* S := g.codRestrict S (fun x => hg ⟨x,rfl⟩)
  have hh : f' = g' := perfect_lift_unique (q.comp S.subtype) h f' g' he
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun hh x)

structure ActualLawfulTable (q : H →* Q) (v : (Ω → E) →* Q) where
  carrier : Subgroup H
  law : CentralOn q carrier
  model : carrier →* (Ω → E)
  onto : Function.Surjective model
  projection : q.comp carrier.subtype = v.comp model

namespace ActualLawfulTable

variable {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem kernel_central : T.model.ker ≤ Subgroup.center T.carrier := by
  intro x hx
  apply T.law
  change q x.val = 1
  have he := DFunLike.congr_fun T.projection x
  change q x.val = v (T.model x) at he
  rw [he,show T.model x = 1 from hx,map_one]

variable [Group.IsPerfect E]

noncomputable def sector (U : Set Ω) : UniversalExtension E →* H :=
  T.carrier.subtype.comp (universalLift T.model T.onto T.kernel_central (sectorMask U))

theorem sector_mem (U : Set Ω) (s : UniversalExtension E) : T.sector U s ∈ T.carrier :=
  (universalLift T.model T.onto T.kernel_central (sectorMask U) s).property

theorem sector_projection (U : Set Ω) :
    q.comp (T.sector U) = (v.comp (sectorMask U)).comp (universalProjection E) := by
  unfold sector
  rw [← MonoidHom.comp_assoc,T.projection,MonoidHom.comp_assoc,
    universalLift_spec,← MonoidHom.comp_assoc]

@[simp] theorem sector_projection_apply (U : Set Ω) (s : UniversalExtension E) :
    q (T.sector U s) = v (sectorMask U (universalProjection E s)) :=
  DFunLike.congr_fun (T.sector_projection U) s

theorem sector_commute {U V : Set Ω} (h : Disjoint U V)
    (s t : UniversalExtension E) : Commute (T.sector U s) (T.sector V t) := by
  have hc := perfect_maps_commute_of_central T.model T.kernel_central
    (universalLift T.model T.onto T.kernel_central (sectorMask U))
    (universalLift T.model T.onto T.kernel_central (sectorMask V))
    (fun s t => by
      have hU := DFunLike.congr_fun (universalLift_spec T.model T.onto T.kernel_central (sectorMask U)) s
      have hV := DFunLike.congr_fun (universalLift_spec T.model T.onto T.kernel_central (sectorMask V)) t
      simp only [MonoidHom.comp_apply] at hU hV
      rw [hU,hV]
      exact sectorMask_commute h _ _) s t
  exact congrArg Subtype.val hc.eq

theorem sector_union {U V : Set Ω} (h : Disjoint U V) :
    T.sector (U ∪ V) = commutingProduct (T.sector U) (T.sector V)
      (T.sector_commute h) := by
  apply T.law.lift_unique q T.carrier
  · rintro x ⟨s,rfl⟩
    exact T.sector_mem _ s
  · rintro x ⟨s,rfl⟩
    exact T.carrier.mul_mem (T.sector_mem _ s) (T.sector_mem _ s)
  · ext s
    simp only [MonoidHom.comp_apply, commutingProduct_apply, map_mul]
    rw [T.sector_projection_apply,T.sector_projection_apply,T.sector_projection_apply]
    simp only [sectorMask_disjoint_union h,map_mul]

@[simp] theorem sector_empty : T.sector ∅ = 1 := by
  apply T.law.lift_unique q T.carrier
  · rintro x ⟨s,rfl⟩
    exact T.sector_mem _ s
  · intro x hx
    rw [MonoidHom.range_one] at hx
    have hx' : x = 1 := hx
    rw [hx']
    exact T.carrier.one_mem
  · rw [T.sector_projection]
    ext s
    simp only [MonoidHom.comp_apply,MonoidHom.one_apply,map_one]
    have he : sectorMask (∅ : Set Ω) (universalProjection E s) = 1 := by ext ω; simp [sectorMask]
    rw [he,map_one]

theorem sector_eq (U : Set Ω) (f : UniversalExtension E →* H)
    (hf : f.range ≤ T.carrier)
    (hp : q.comp f = (v.comp (sectorMask U)).comp (universalProjection E)) :
    T.sector U = f :=
  T.law.lift_unique q T.carrier _ _ (by rintro x ⟨s,rfl⟩; exact T.sector_mem U s) hf
    ((T.sector_projection U).trans hp.symm)

end ActualLawfulTable

section FamilyModel
variable {ι : Type*} (U : ι → Set Ω) (F : Option ι → E →* H)
    (q : H →* Q) (v : (Ω → E) →* Q)
    (hv : Function.Injective v)
    (hcompat : ∀ i, q.comp (F i) = v.comp (maskFamily U i))

include hcompat in
theorem copyFamilyEval_projection : q.comp (copyFamilyEval F) = v.comp (assignmentEval U) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  simpa only [MonoidHom.comp_apply,assignmentEval,copyFamilyEval_of] using
    DFunLike.congr_fun (hcompat i) s

noncomputable def actualFamilyModel : (copyFamilyEval F).range →* (Ω → E) :=
  (copyFamilyEval F).rangeRestrict.liftOfSurjective
    (copyFamilyEval F).rangeRestrict_surjective ⟨assignmentEval U, by
      intro w hw
      apply hv
      have hh := DFunLike.congr_fun (copyFamilyEval_projection U F q v hcompat) w
      change q (copyFamilyEval F w) = v (assignmentEval U w) at hh
      have hw' : copyFamilyEval F w = 1 := congrArg Subtype.val hw
      rw [hw',map_one] at hh
      simpa only [map_one] using hh.symm⟩

theorem actualFamilyModel_comp :
    (actualFamilyModel U F q v hv hcompat).comp (copyFamilyEval F).rangeRestrict =
      assignmentEval U :=
  (copyFamilyEval F).rangeRestrict.liftOfRightInverse_comp _ _ _

theorem actualFamilyModel_projection :
    q.comp (copyFamilyEval F).range.subtype = v.comp (actualFamilyModel U F q v hv hcompat) := by
  ext x
  obtain ⟨w,rfl⟩ := (copyFamilyEval F).rangeRestrict_surjective x
  have he := DFunLike.congr_fun (actualFamilyModel_comp U F q v hv hcompat) w
  change actualFamilyModel U F q v hv hcompat ((copyFamilyEval F).rangeRestrict w) =
    assignmentEval U w at he
  simp only [MonoidHom.comp_apply]
  rw [he]
  exact DFunLike.congr_fun (copyFamilyEval_projection U F q v hcompat) w

noncomputable def actualFamilyTable [Group.IsPerfect E] [Finite ι] [Finite Ω]
    (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω = ν)
    (h : CentralOn q (copyFamilyEval F).range) : ActualLawfulTable q v where
  carrier := (copyFamilyEval F).range
  law := h
  model := actualFamilyModel U F q v hv hcompat
  onto := by
    intro s
    obtain ⟨w,rfl⟩ := assignmentEval_surjective U hsep s
    exact ⟨(copyFamilyEval F).rangeRestrict w,
      DFunLike.congr_fun (actualFamilyModel_comp U F q v hv hcompat) w⟩
  projection := actualFamilyModel_projection U F q v hv hcompat

end FamilyModel
end ActualSectors

end SimpleAmenable
end
end

end OAI

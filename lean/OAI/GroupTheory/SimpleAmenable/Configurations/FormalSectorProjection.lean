import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairControl
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalSectorSubfamily
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalStarTables

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalSectorProjection
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]

theorem alternating_function_center (hα : 4 ≤ Nat.card α) :
    Subgroup.center (Ω → alternatingGroup α)=⊥ := by
  rw [Subgroup.center_pi]
  simp only [alternatingGroup.center_eq_bot hα,Subgroup.pi_bot]

theorem assignmentPullback_surjective {X Y E : Type*} [Group E] (v : X → Y)
    (hv : Function.Injective v) : Function.Surjective (assignmentPullback (E := E) v) := by
  classical
  intro f
  refine ⟨Function.extend v f (fun _ => 1),?_⟩
  ext x
  exact congrFun (Function.extend_comp hv f (fun _ => 1)) x

namespace FormalStarTable
variable [Group.IsPerfect (alternatingGroup α)] [Finite ι]
    {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

theorem sector_projection (hα : 4 ≤ Nat.card α)
    (q : H →* Q) (ρ : (Ω → alternatingGroup α) →* Q) (hρ : Function.Injective ρ)
    (δ : ((ι → Bool) → alternatingGroup α) →* (Ω → alternatingGroup α))
    (hδ : Function.Surjective δ)
    (hp : ∀ i, q.comp (F i)=ρ.comp (δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _))))
    (V : Set (ι → Bool)) (s : TrackStar α) :
    q (T.sector V s)=ρ (δ (sectorMask V (universalProjection _ s))) := by
  let e := copyFamilyEval T.input
  let v := δ.comp (formalAssignmentEval (universalProjection (alternatingGroup α)))
  have hv : Function.Surjective v := hδ.comp (formalAssignmentEval_surjective
    (universalProjection (alternatingGroup α)) (universalProjection_surjective _))
  have he : (q.comp T.carrier.subtype).comp e=ρ.comp v := by
    rw [MonoidHom.comp_assoc,T.input_eval]
    apply FreeGroup.ext_hom
    rintro ⟨i,t⟩
    have hh := DFunLike.congr_fun (hp i) t
    simpa only [MonoidHom.comp_apply,v,formalAssignmentEval,copySourceMap,FreeGroup.map.of,
      assignmentEval,copyFamilyEval_of] using hh
  have hk : ∀ w, e w=1 → v w=1 := by
    intro w hw
    apply hρ
    have hh := DFunLike.congr_fun he w
    change q ((e w).val)=ρ (v w) at hh
    rw [hw,Subgroup.coe_one,map_one] at hh
    simpa only [map_one] using hh.symm
  let γ : T.carrier →* (Ω → alternatingGroup α) :=
    e.liftOfSurjective T.input_surjective ⟨v,hk⟩
  have hγe : γ.comp e=v := e.liftOfRightInverse_comp _ _ _
  have hγ : Function.Surjective γ := by
    intro x
    obtain ⟨w,rfl⟩ := hv x
    exact ⟨e w,DFunLike.congr_fun hγe w⟩
  have hγp : q.comp T.carrier.subtype=ρ.comp γ := by
    apply (MonoidHom.cancel_right T.input_surjective).mp
    change (q.comp T.carrier.subtype).comp e=(ρ.comp γ).comp e
    change (q.comp T.carrier.subtype).comp e=ρ.comp (γ.comp e)
    rw [hγe]
    exact he
  have hγi (i : Option ι) : γ.comp (T.input i)=δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _)) := by
    apply MonoidHom.ext
    intro t
    have hh := DFunLike.congr_fun hγe (FreeGroup.of (i,t))
    simpa only [MonoidHom.comp_apply,e,v,copyFamilyEval_of,formalAssignmentEval,
      copySourceMap,FreeGroup.map.of,assignmentEval] using hh
  have hs := T.sector_forward γ hγ (alternating_function_center hα) δ hγi V s
  have hh := DFunLike.congr_fun hγp (centralSector T.model V s)
  simpa only [MonoidHom.comp_apply,sector,hs] using hh

end FormalStarTable
end FormalSectorProjection

end SimpleAmenable
end
end

end OAI

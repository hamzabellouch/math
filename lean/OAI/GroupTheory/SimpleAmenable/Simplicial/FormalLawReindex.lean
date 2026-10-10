import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallFamilyWords
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallFamilyGlobal

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalLawReindex
variable {α ι κ H : Type*} [Fintype α] [DecidableEq α] [Group H]

noncomputable def smallFamilyReindex (v : κ → ι) : SmallFamilyWord α κ →* SmallFamilyWord α ι :=
  FreeGroup.map (fun l => ⟨l.1,l.2.1.map v,l.2.2⟩)

theorem smallFamilyEval_reindex
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) (v : κ → ι) :
    smallFamilyEval (fun I i => F I (i.map v))=(smallFamilyEval F).comp (smallFamilyReindex v) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  simp only [MonoidHom.comp_apply,smallFamilyReindex,FreeGroup.map.of,smallFamilyEval_of]

theorem smallFormalModel_reindex (v : κ → ι) :
    (smallFamilyModel (α := α) (fun i : ι => {σ : ι → Bool | σ i=true})).comp (smallFamilyReindex v)=
      (assignmentPullback (fun σ : ι → Bool => σ ∘ v)).comp
        (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true})) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  ext σ
  simp only [MonoidHom.comp_apply,smallFamilyReindex,FreeGroup.map.of,smallFamilyModel,smallFamilyEval_of]
  cases i <;> simp [maskFamily,sectorMask,assignmentPullback,Function.comp_def]

theorem smallFormalLaw_reindex
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (h : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval F).rangeRestrict) (v : κ → ι) :
    HasCentralLaw (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true}))
      (smallFamilyEval (fun I i => F I (i.map v))).rangeRestrict := by
  rw [hasCentralLaw_iff]
  intro w hw
  have hm : smallFamilyModel (α := α) (fun i : ι => {σ : ι → Bool | σ i=true})
      (smallFamilyReindex v w)=1 := by
    have he := DFunLike.congr_fun (smallFormalModel_reindex (α := α) v) w
    simp only [MonoidHom.comp_apply,hw,map_one] at he
    exact he
  have hz := (hasCentralLaw_iff _ _).mp h _ hm
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨x,⟨z,rfl⟩⟩
  apply Subtype.ext
  have he := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz
    ((smallFamilyEval F).rangeRestrict (smallFamilyReindex v z)))
  change smallFamilyEval F (smallFamilyReindex v z)*smallFamilyEval F (smallFamilyReindex v w)=
    smallFamilyEval F (smallFamilyReindex v w)*smallFamilyEval F (smallFamilyReindex v z) at he
  change smallFamilyEval (fun I i => F I (i.map v)) z*smallFamilyEval (fun I i => F I (i.map v)) w=
    smallFamilyEval (fun I i => F I (i.map v)) w*smallFamilyEval (fun I i => F I (i.map v)) z
  simpa only [smallFamilyEval_reindex,MonoidHom.comp_apply] using he

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

omit [Finite ι] in
theorem smallPrimitive_formal_reindex [Finite κ] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict) (v : κ → ι) :
    HasCentralLaw (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).rangeRestrict := by
  have he : B.smallPrimitiveInputs hlarge (P ∘ v)=
      fun I i => B.smallPrimitiveInputs hlarge P I (i.map v) := by
    funext I i
    cases i <;> rfl
  rw [he]
  exact smallFormalLaw_reindex _ h v

end InitialCoverSystem
end FormalLawReindex

end SimpleAmenable
end
end

end OAI

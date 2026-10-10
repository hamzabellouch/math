import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageRealization
import OAI.GroupTheory.SimpleAmenable.Configurations.StageFiberSum

namespace OAI

section

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n s : ℕ} (P : BooleanPartition a) (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i) (hLi : Function.Injective L)
open UniformObject
lemma fiberMap_realize {U V : Obj P (s:=s)} (f : U ⟶ V) (b : Fin P.size × Fin s)
    (x : Fin (U b).size) :
    fiberMap ((realize P L hL).map f) b (fiberPoint P L hL U b x)=fiberPoint P L hL V b (f b x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change indexMap P L hL f (index P U ⟨b,x⟩)=index P V ⟨b,f b x⟩
    change (index P V) ((trackMap P f) ((index P U).symm ((index P U) ⟨b,x⟩)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  · rfl
noncomputable def evaluationRealize : 𝟭 (Obj P (s:=s)) ≅ realize P L hL ⋙ evaluation := by
  refine NatIso.ofComponents (fun U => asIso (show U ⟶ E.obj ((realize P L hL).obj U) from
    fun b => (fiberEquiv P L hL hLi U b).trans (enumerate ((realize P L hL).obj U) b))) ?_
  intro U V f
  funext b
  apply Equiv.ext
  intro x
  change enumerate ((realize P L hL).obj V) b (fiberPoint P L hL V b (f b x))=
    E.map ((realize P L hL).map f) b (enumerate ((realize P L hL).obj U) b (fiberPoint P L hL U b x))
  exact ((E_map_enum ((realize P L hL).map f) b (fiberPoint P L hL U b x)).trans
    (congrArg (enumerate ((realize P L hL).obj V) b) (fiberMap_realize P L hL f b x))).symm

include hL hLi

theorem evaluationEssSurj : (evaluation (P:=P) (L:=L)).EssSurj := {
  mem_essImage U := ⟨(realize P L hL).obj U,⟨(evaluationRealize P L hL hLi).app U |>.symm⟩⟩ }

theorem evaluationFull : (evaluation (P:=P) (L:=L)).Full := by
  let R := realize P L hL
  have : R.EssSurj := realize_essSurj P L hL hLi
  have : (R ⋙ evaluation (P:=P) (L:=L)).IsEquivalence :=
    Functor.isEquivalence_of_iso (evaluationRealize P L hL hLi)
  apply Functor.full_of_comp_essSurj (evaluation (P:=P) (L:=L)) R
  intro X Y φ
  refine ⟨R.map ((R ⋙ evaluation).preimage φ), ?_⟩
  exact (R ⋙ evaluation).map_preimage φ

theorem evaluationIsEquivalence : (evaluation (P:=P) (L:=L)).IsEquivalence := {
  faithful := inferInstance
  full := evaluationFull P L hL hLi
  essSurj := evaluationEssSurj P L hL hLi }
end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI

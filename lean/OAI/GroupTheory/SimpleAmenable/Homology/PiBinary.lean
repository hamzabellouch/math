import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PiFiber

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet

noncomputable def binaryIso (X:Fin 2→SSet) : obj X ≅ X 0⊗X 1 where
  hom := {app _:=↾fun z=>(z 0,z 1)
          naturality _ _ _:=rfl}
  inv := {app _:=↾fun z=>Fin.cases z.1 (Fin.cases z.2 (fun i=>i.elim0))
          naturality _ _ _:=by apply ConcreteCategory.hom_ext; intro z; funext i; fin_cases i <;> rfl}
  hom_inv_id:=by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro z; funext i; fin_cases i <;> rfl
  inv_hom_id:=by ext p z <;> rfl
@[simp] lemma binaryIso_fst (X:Fin 2→SSet) : (binaryIso X).hom ≫ CartesianMonoidalCategory.fst _ _=proj X 0 := rfl
@[simp] lemma binaryIso_snd (X:Fin 2→SSet) : (binaryIso X).hom ≫ CartesianMonoidalCategory.snd _ _=proj X 1 := rfl
end PiSSet
namespace PiFiber

variable (C:Type) [Groupoid.{0} C]
lemma binary_inclusion (p:Fin 2→Skeleton C) :
    inclusion C (Fin 2) p ≫ (PiSSet.binaryIso (fun _:Fin 2=>nerve C)).hom =
      (PiSSet.binaryIso (fun i=>nerve (ComponentTranslation.Fiber (p i)))).hom ≫
        (nerveMap (ComponentTranslation.property (p 0)).ι⊗ₘnerveMap (ComponentTranslation.property (p 1)).ι) := rfl
end PiFiber

end

end OAI

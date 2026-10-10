import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalFunctor

namespace OAI

section
open CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def oneEval : Diagram C (Fin 2) ⥤ C := eval 1 ⋙ Pi.eval (fun _:Fin 1=>C) 0
noncomputable def oneConst : C ⥤ (Fin 1→C) := Functor.pi' (fun _=>𝟭 C)
noncomputable def piOneEquiv : (Fin 1→C) ≌ C where
  functor := Pi.eval (fun _:Fin 1=>C) 0
  inverse := oneConst
  unitIso := NatIso.ofComponents (fun values =>
    Pi.isoMk (fun index => eqToIso (congrArg values (Subsingleton.elim index 0)))) (by
      intro source target morphism
      funext index
      have index_eq : index = 0 := Subsingleton.elim _ _
      subst index
      change morphism 0 ≫ eqToHom (rfl : target 0 = target 0) =
        eqToHom (rfl : source 0 = source 0) ≫ morphism 0
      simp)
  counitIso := Iso.refl _
  functor_unitIso_comp values := by
    change eqToHom (rfl : values 0 = values 0) ≫ 𝟙 (values 0) = 𝟙 (values 0)
    simp
noncomputable instance oneEval_equivalence : (oneEval (C:=C)).IsEquivalence := by
  have : (Pi.eval (fun _:Fin 1=>C) 0).IsEquivalence := (piOneEquiv (C:=C)).isEquivalence_functor
  dsimp only [oneEval]
  infer_instance
noncomputable def tensorPair : (Fin 2→C) ⥤ C where
  obj X := X 0 ⊗ X 1
  map f := f 0 ⊗ₘ f 1
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]
noncomputable def binaryCut : eval (C:=C) 2 ⋙ tensorPair ⟶
    reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom ⋙ oneEval where
  app D := (D.cut 0 1 2 (by decide) (by decide)).hom
  naturality D E f := f.cut 0 1 2 (by decide) (by decide)
lemma binary_zero : reindex (C:=C) (SimplexCategory.δ (0:Fin 3)).toOrderHom ⋙ oneEval =
    eval 2 ⋙ Pi.eval (fun _:Fin 2=>C) 1 := rfl
lemma binary_last : reindex (C:=C) (SimplexCategory.δ (2:Fin 3)).toOrderHom ⋙ oneEval =
    eval 2 ⋙ Pi.eval (fun _:Fin 2=>C) 0 := rfl
noncomputable def binaryFace (i:Fin 3) : (Fin 2→C) ⥤ C :=
  (eval 2).asEquivalence.inverse ⋙ reindex (SimplexCategory.δ i).toOrderHom ⋙ oneEval
noncomputable def binaryFaceZero : binaryFace (C:=C) 0 ≅ Pi.eval (fun _:Fin 2=>C) 1 :=
  Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse (eqToIso binary_zero) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
noncomputable def binaryFaceLast : binaryFace (C:=C) 2 ≅ Pi.eval (fun _:Fin 2=>C) 0 :=
  Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse (eqToIso binary_last) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
noncomputable def binaryCutIso : eval (C:=C) 2 ⋙ tensorPair ≅
    reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom ⋙ oneEval :=
  NatIso.ofComponents (fun D => D.cut 0 1 2 (by decide) (by decide)) (by
    intro D E f; exact f.cut 0 1 2 (by decide) (by decide))
noncomputable def binaryFaceMiddle : binaryFace (C:=C) 1 ≅ tensorPair :=
  (Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse binaryCutIso).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
end IntervalBar.Diagram

end

end OAI

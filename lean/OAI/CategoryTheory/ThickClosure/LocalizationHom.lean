import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LocalizationHom
open CategoryTheory
universe u v w v'

theorem map_bijective_of_inverts (C : Type u) [Category.{v} C]
    (E : Type w) [Category.{v'} E] (W : MorphismProperty C)
    (L : C ⥤ E) [L.IsLocalization W] (X Y : C)
    (h : W.IsInvertedBy (coyoneda.obj (Opposite.op X))) :
    Function.Bijective (L.map : (X ⟶ Y) → (L.obj X ⟶ L.obj Y)) := by
  let F := coyoneda.obj (Opposite.op X) ⋙ uliftFunctor.{v',v}
  have hF : W.IsInvertedBy F := MorphismProperty.IsInvertedBy.of_comp W _ h _
  let F' := Localization.lift F hF L
  let e : L ⋙ F' ≅ F := Localization.fac F hF L
  let U := coyoneda.obj (Opposite.op (L.obj X)) ⋙ uliftFunctor.{v,v'}
  let j : F ⟶ L ⋙ U :=
    { app := fun A => ↾fun f => ULift.up (L.map f.down)
      naturality := by intro A B f; ext g; exact congrArg ULift.up (L.map_comp g.down f) }
  let j' : F' ⟶ U := Localization.liftNatTrans L W F (L ⋙ U) F' U j
  have hj (A : C) : j'.app (L.obj A) = e.hom.app A ≫ j.app A := by
    dsimp only [j']
    rw [Localization.liftNatTrans_app]
    rfl
  let x : F'.obj (L.obj X) := e.inv.app X (ULift.up (𝟙 X))
  let invMap (f : L.obj X ⟶ L.obj Y) : X ⟶ Y :=
    (e.hom.app Y (F'.map f x)).down
  have hex : e.hom.app X x = ULift.up (𝟙 X) := by
    have he := ConcreteCategory.congr_hom (e.inv_hom_id_app X)
      (show F.obj X from ULift.up (𝟙 X))
    exact he
  have leftInv (f : X ⟶ Y) : invMap (L.map f) = f := by
    have he := ConcreteCategory.congr_hom (e.hom.naturality f) x
    change e.hom.app Y (F'.map (L.map f) x) =
      ULift.up ((e.hom.app X x).down ≫ f) at he
    rw [hex, Category.id_comp] at he
    exact congrArg ULift.down he
  have hx : j'.app (L.obj X) x = ULift.up (𝟙 (L.obj X)) := by
    rw [hj]
    change ULift.up (L.map (e.hom.app X x).down) = _
    rw [hex, L.map_id]
  have rightInv (f : L.obj X ⟶ L.obj Y) : L.map (invMap f) = f := by
    have hnat := ConcreteCategory.congr_hom (j'.naturality f) x
    change j'.app (L.obj Y) (F'.map f x) =
      ULift.up ((j'.app (L.obj X) x).down ≫ f) at hnat
    rw [hx, hj] at hnat
    change ULift.up (L.map ((e.hom.app Y (F'.map f x)).down)) =
      ULift.up (𝟙 (L.obj X) ≫ f) at hnat
    simpa only [Category.id_comp] using congrArg ULift.down hnat
  exact ⟨Function.LeftInverse.injective leftInv, Function.RightInverse.surjective rightInv⟩

theorem map_bijective (C : Type u) [Category.{v} C]
    (E : Type w) [Category.{v} E] (W : MorphismProperty C)
    (L : C ⥤ E) [L.IsLocalization W] (X Y : C)
    (h : W.IsInvertedBy (coyoneda.obj (Opposite.op X))) :
    Function.Bijective (L.map : (X ⟶ Y) → (L.obj X ⟶ L.obj Y)) :=
  map_bijective_of_inverts C E W L X Y h

end HahnWilson.LocalizationHom

end

end OAI

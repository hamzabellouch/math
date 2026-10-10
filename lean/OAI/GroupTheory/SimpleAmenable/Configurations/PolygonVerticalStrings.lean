import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStringGroupoid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonVerticalStrings

open Classical CategoryTheory
namespace PolygonObject
variable {a n m : ℕ}

def verticalStringProperty (a n : ℕ) : ObjectProperty (RawString a n) :=
  fun F => ∀ (i j : Fin (n+1)) (f : i ⟶ j), Positional (F.map f)

abbrev VerticalString (a n : ℕ) := (verticalStringProperty a n).FullSubcategory

noncomputable def verticalEvaluation (a n : ℕ) : VerticalString a n ⥤ PolygonObject a where
  obj F := F.obj.obj 0
  map f := f.hom.app 0

noncomputable def verticalConstant (a n : ℕ) : PolygonObject a ⥤ VerticalString a n where
  obj U := ⟨(Functor.const (Fin (n+1))).obj U,fun _ _ _ => identity_positional U⟩
  map f := ObjectProperty.homMk ((Functor.const (Fin (n+1))).map f)

noncomputable instance verticalEvaluation_full : (verticalEvaluation a n).Full where
  map_surjective h := ⟨ObjectProperty.homMk (extendLadder h),extendLadder_zero h⟩

instance verticalEvaluation_faithful : (verticalEvaluation a n).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    exact ladder_ext h

instance verticalEvaluation_essSurj : (verticalEvaluation a n).EssSurj where
  mem_essImage U := ⟨(verticalConstant a n).obj U,⟨Iso.refl U⟩⟩

instance verticalEvaluation_isEquivalence : (verticalEvaluation a n).IsEquivalence where

noncomputable def verticalEquivalence (a n : ℕ) : VerticalString a n ≌ PolygonObject a :=
  (verticalEvaluation a n).asEquivalence

noncomputable def verticalReindex (u : Fin (n+1) ⥤ Fin (m+1)) :
    VerticalString a m ⥤ VerticalString a n where
  obj F := ⟨u⋙F.obj,fun i j f => F.property (u.obj i) (u.obj j) (u.map f)⟩
  map f := ObjectProperty.homMk (Functor.whiskerLeft u f.hom)
  map_id F := by apply ObjectProperty.hom_ext; rfl
  map_comp f g := by apply ObjectProperty.hom_ext; rfl

@[simp] theorem verticalConstant_evaluation (a n : ℕ) :
    verticalConstant a n ⋙ verticalEvaluation a n=𝟭 (PolygonObject a) := rfl

instance verticalConstant_isEquivalence : (verticalConstant a n).IsEquivalence := by
  have : (verticalConstant a n ⋙ verticalEvaluation a n).IsEquivalence := by
    rw [verticalConstant_evaluation]
    infer_instance
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    (verticalConstant a n) (verticalEvaluation a n)

theorem verticalConstant_reindex (u : Fin (n+1) ⥤ Fin (m+1)) :
    verticalConstant a m ⋙ verticalReindex u=verticalConstant a n := by
  apply CategoryTheory.Functor.ext
  · intro U V f; rfl
  · intro U; rfl

end PolygonObject
end PolygonVerticalStrings

end SimpleAmenable
end
end

end OAI

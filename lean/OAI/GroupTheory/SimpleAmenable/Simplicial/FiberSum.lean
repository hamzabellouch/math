import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal

namespace OAI

open CategoryTheory Limits MonoidalCategory
namespace BarFiberProduct

section
variable {C D : Type} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]
noncomputable instance prodBraided : BraidedCategory (C×D) where
  braiding X Y := (β_ X.1 Y.1).prod (β_ X.2 Y.2)
  braiding_naturality_left := by intro X Y f Z; ext <;> simp
  braiding_naturality_right := by intro X Y Z f; ext <;> simp
  hexagon_forward := by intro X Y Z; ext <;> simp
  hexagon_reverse := by intro X Y Z; ext <;> simp
end
variable {C D : Type} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
noncomputable instance prodSymmetric :
    SymmetricCategory (C×D) where
  symmetry X Y := by
    apply Prod.hom_ext
    · change (β_ X.1 Y.1).hom ≫ (β_ Y.1 X.1).hom=𝟙 _
      simp
    · change (β_ X.2 Y.2).hom ≫ (β_ Y.2 X.2).hom=𝟙 _
      simp
end BarFiberProduct
open BarFiberProduct
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid

lemma tensorμ_eq (A B C D : FiniteSetGroupoid) :
    tensorμ A B C D = assoc A B (sum C D) ≫
      sumHom (𝟙 A) (CategoryTheory.inv (assoc B C D)) ≫
      sumHom (𝟙 A) (sumHom (swap B C) (𝟙 D)) ≫
      sumHom (𝟙 A) (assoc C B D) ≫ CategoryTheory.inv (assoc A C (sum B D)) := rfl
lemma tensorμ_swap (U V : FiniteSetGroupoid × FiniteSetGroupoid) :
    tensorμ U.1 U.2 V.1 V.2 ≫ sumHom (swap U.1 V.1) (swap U.2 V.2) =
      swap (sum U.1 U.2) (sum V.1 V.2) ≫ tensorμ V.1 V.2 U.1 U.2 := by
    rw [tensorμ_eq,tensorμ_eq]
    dsimp only [CategoryStruct.comp, instGroupoid, toEquiv]
    apply Equiv.ext; intro x
    obtain ⟨y,rfl⟩ := (sumEquiv (sum U.1 U.2) (sum V.1 V.2)).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumEquiv U.1 U.2).surjective y
      cases z <;> simp [toEquiv, sumHom, assoc, swap, inv_eq, Equiv.trans_apply, MonoidalCategory.tensorObj]
    | inr y =>
      obtain ⟨z,rfl⟩ := (sumEquiv V.1 V.2).surjective y
      cases z <;> simp [toEquiv, sumHom, assoc, swap, inv_eq, Equiv.trans_apply, MonoidalCategory.tensorObj]
noncomputable instance tensorBraided : (tensor FiniteSetGroupoid).Braided where
  braided U V := tensorμ_swap U V
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end OAI

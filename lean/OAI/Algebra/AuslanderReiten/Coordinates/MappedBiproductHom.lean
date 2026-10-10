import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Module.Prod

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u v w v' w'
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {D : Type w'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] (X : D) (Y Z : C) [HasBinaryBiproduct Y Z]

def mappedBiproductHomEquiv : (X ⟶ F.obj (Y ⊞ Z)) ≃ₗ[k]
    ((X ⟶ F.obj Y) × (X ⟶ F.obj Z)) where
  toFun f := (f ≫ F.map biprod.fst, f ≫ F.map biprod.snd)
  invFun p := p.1 ≫ F.map biprod.inl + p.2 ≫ F.map biprod.inr
  left_inv f := by
    dsimp
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id, Category.comp_id]
  right_inv p := by
    ext <;> simp [Preadditive.add_comp, Category.assoc, ← F.map_comp]
  map_add' f g := by ext <;> simp [Preadditive.add_comp]
  map_smul' a f := by ext <;> simp

@[simp] theorem mappedBiproductHomEquiv_fst (f : X ⟶ F.obj (Y ⊞ Z)) :
    (mappedBiproductHomEquiv k F X Y Z f).1 = f ≫ F.map biprod.fst := rfl

@[simp] theorem mappedBiproductHomEquiv_snd (f : X ⟶ F.obj (Y ⊞ Z)) :
    (mappedBiproductHomEquiv k F X Y Z f).2 = f ≫ F.map biprod.snd := rfl

end ArExplicit

end

end OAI

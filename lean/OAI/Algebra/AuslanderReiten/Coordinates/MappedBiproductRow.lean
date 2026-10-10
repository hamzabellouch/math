import OAI.Algebra.AuslanderReiten.Coordinates.MappedBiproductHom

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u v w v' w'
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {D : Type w'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] (X : D) (Y Z : C) [HasBinaryBiproduct Y Z]

theorem mappedBiproduct_row {W : C} (b : Y ⊞ Z ⟶ W) (v : X ⟶ F.obj (Y ⊞ Z)) :
    v ≫ F.map b =
      (mappedBiproductHomEquiv k F X Y Z v).1 ≫ F.map (biprod.inl ≫ b) +
      (mappedBiproductHomEquiv k F X Y Z v).2 ≫ F.map (biprod.inr ≫ b) := by
  calc
    v ≫ F.map b = v ≫ F.map ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ b) := by
      rw [biprod.total, Category.id_comp]
    _ = _ := by
      simp only [Functor.map_comp, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, mappedBiproductHomEquiv_fst, mappedBiproductHomEquiv_snd,
        Category.assoc]

end ArExplicit

end

end OAI

import Mathlib.Data.Fintype.Sum
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Shift.CommShift

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]

/-- Distribute a finite biproduct of binary biproducts and retain the two branch labels. -/
def biproductBiprod {I : Type} [Fintype I] (f g : I → C) :
    (⨁ fun i => f i ⊞ g i) ≅ ⨁ (Sum.elim f g) where
  hom := biproduct.desc fun i => biprod.desc
    (biproduct.ι (Sum.elim f g) (Sum.inl i)) (biproduct.ι (Sum.elim f g) (Sum.inr i))
  inv := biproduct.desc fun x => match x with
    | .inl i => biprod.inl ≫ biproduct.ι (fun i => f i ⊞ g i) i
    | .inr i => biprod.inr ≫ biproduct.ι (fun i => f i ⊞ g i) i
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    apply biprod.hom_ext'
    · simp only [biproduct.ι_desc_assoc, Category.comp_id]
      erw [biprod.inl_desc_assoc, biproduct.ι_desc]
      rfl
    · simp only [biproduct.ι_desc_assoc, Category.comp_id]
      erw [biprod.inr_desc_assoc, biproduct.ι_desc]
      rfl
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro x
    cases x <;> erw [biproduct.ι_desc_assoc]
    · erw [Category.assoc, biproduct.ι_desc]
      erw [biprod.inl_desc, Category.comp_id]
    · erw [Category.assoc, biproduct.ι_desc]
      erw [biprod.inr_desc, Category.comp_id]

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Shift a binary splitting, using the actual shift functors and their addition isomorphism. -/
def splitShift (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
    (X Z : C) (b d t : ℤ) (split : Phi.obj X ≅ Z⟦b⟧ ⊞ Z⟦b+d⟧) :
    Phi.obj (X⟦t⟧) ≅ Z⟦b+t⟧ ⊞ Z⟦b+d+t⟧ :=
  (Phi.commShiftIso t).app X ≪≫ (shiftFunctor C t).mapIso split ≪≫
    (shiftFunctor C t).mapBiprod _ _ ≪≫
    biprod.mapIso (shiftAdd Z b t).symm (shiftAdd Z (b+d) t).symm
end ExternalTensor.Binomial

end

end OAI

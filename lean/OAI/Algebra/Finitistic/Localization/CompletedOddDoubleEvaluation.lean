import OAI.Algebra.Finitistic.Localization.CompletedShiftedCornerEvaluation
import OAI.Algebra.Finitistic.Localization.CompletedCornerEvaluation
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
private theorem mapBiprod_square {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]
    {A B : C} {X Y : D} (a : A ⟶ A) (b : B ⟶ B) (x : X ⟶ X) (y : Y ⟶ Y)
    (e : F.obj A ≅ X) (f : F.obj B ≅ Y)
    (ha : F.map a ≫ e.hom = e.hom ≫ x) (hb : F.map b ≫ f.hom = f.hom ≫ y) :
    F.map (biprod.map a b) ≫ (F.mapBiprod A B ≪≫ biprod.mapIso e f).hom =
      (F.mapBiprod A B ≪≫ biprod.mapIso e f).hom ≫ biprod.map x y := by
  apply biprod.hom_ext
  · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
      Category.assoc, biprod.map_fst, biprod.map_fst_assoc, biprod.lift_fst_assoc]
    rw [← Category.assoc, ← Functor.map_comp, biprod.map_fst, Functor.map_comp,
      Category.assoc, ha]
  · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
      Category.assoc, biprod.map_snd, biprod.map_snd_assoc, biprod.lift_snd_assoc]
    rw [← Category.assoc, ← Functor.map_comp, biprod.map_snd, Functor.map_comp,
      Category.assoc, hb]

universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)
local instance : HasFiniteBiproducts (Karoubi (BoundedQ P)) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (BoundedQ P)) := hasBinaryBiproducts_of_finite_biproducts _

local instance : PreservesBinaryBiproducts (completedDerivedEvaluation X) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Evaluation of the formal odd double used in Section 3. -/
def completedOddDoubleImageIso (r : PresentedAlgebra P) (hr : r*r=r) (n : ℤ) :
    (completedDerivedEvaluation X).obj
      (quotientSummand r hr ⊞
        ((functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n)).obj
          (quotientSummand r hr)) ≅
    evaluatedImageDerived X r ⊞ (evaluatedImageDerived X r)⟦n⟧ :=
  (completedDerivedEvaluation X).mapBiprod _ _ ≪≫
    biprod.mapIso (completedSummandImageIso X r hr) (completedShiftedSummandImageIso X r hr n)

/-- The two summands of the evaluated odd double carry exactly the original
corner action and its shift. This is the action used at each diagram vertex. -/
theorem completed_oddDouble_corner_square (e a : PresentedAlgebra P) (he : e*e=e) (n : ℤ) :
    (completedDerivedEvaluation X).map
      (biprod.map (quotientCornerEnd e a he)
        (((functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n)).map
          (quotientCornerEnd e a he))) ≫ (completedOddDoubleImageIso X e he n).hom =
    (completedOddDoubleImageIso X e he n).hom ≫
      biprod.map (evaluatedCornerEnd X e a) ((evaluatedCornerEnd X e a)⟦n⟧') := by
  exact mapBiprod_square (completedDerivedEvaluation X) _ _ _ _
    (completedSummandImageIso X e he) (completedShiftedSummandImageIso X e he n)
    (completed_corner_square X e a he) (completed_shifted_corner_square X e a he n)
end LittleFinitistic.QuadraticEncoding

end

end OAI

import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftNaturality
import Mathlib.CategoryTheory.Linear.Basic

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

def negativeShiftIso : Y ≅ X⟦-n⟧ :=
  ((CategoryTheory.shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).app Y).symm ≪≫
    (CategoryTheory.shiftFunctor C (-n)).mapIso e.symm

def shiftedNegativeIso (a : ℤ) : Y⟦a⟧ ≅ X⟦a-n⟧ :=
  (CategoryTheory.shiftFunctor C a).mapIso (negativeShiftIso n e) ≪≫
    (CategoryTheory.shiftFunctorAdd' C (-n) a (a-n) (by omega)).symm.app X

variable (k : Type w) [CommRing k] [Preadditive C] [Linear k C]

def shiftedNegativeHomEquiv (S : C) (a : ℤ) :
    (S ⟶ Y⟦a⟧) ≃ₗ[k] (S ⟶ X⟦a-n⟧) :=
  Linear.homCongr k (Iso.refl S) (shiftedNegativeIso n e a)

end ArExplicit

end

end OAI

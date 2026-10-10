import OAI.Algebra.Finitistic.Localization.FormalSummandAction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.BiprodEvaluationSquare
universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]

/-- Transport both diagonal actions through additive evaluation and given summand isomorphisms. -/
theorem square {A B : C} {A' B' : D} (f : A ⟶ A) (g : B ⟶ B)
    (i : F.obj A ≅ A') (j : F.obj B ≅ B') (f' : A' ⟶ A') (g' : B' ⟶ B')
    (hf : F.map f ≫ i.hom = i.hom ≫ f') (hg : F.map g ≫ j.hom = j.hom ≫ g') :
    F.map (biprod.map f g) ≫ (F.mapBiprod A B ≪≫ biprod.mapIso i j).hom =
      (F.mapBiprod A B ≪≫ biprod.mapIso i j).hom ≫ biprod.map f' g' := by
  apply biprod.hom_ext
  · simp only [Iso.trans_hom,Functor.mapBiprod_hom,biprod.mapIso_hom,
      Category.assoc,biprod.map_fst,biprod.map_fst_assoc,biprod.lift_fst_assoc]
    rw [← Category.assoc,← Functor.map_comp,biprod.map_fst,Functor.map_comp,Category.assoc,hf]
  · simp only [Iso.trans_hom,Functor.mapBiprod_hom,biprod.mapIso_hom,
      Category.assoc,biprod.map_snd,biprod.map_snd_assoc,biprod.lift_snd_assoc]
    rw [← Category.assoc,← Functor.map_comp,biprod.map_snd,Functor.map_comp,Category.assoc,hg]

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [Linear k C] [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ,(shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ,(shiftFunctor C n).Linear k]
variable {L : C} (theta : R →ₐ[k] End L) (e : R) (he : e*e=e)
  (hc : ∀ r : R,e*r=r*e) (alpha : R →ₐ[k] R)
local instance : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts _

omit [HasBinaryBiproducts C] in
theorem action_formula (r : R) :
    FormalSummandAction.oddDoubleAction theta e he hc alpha r =
      biprod.map (FormalSummandAction.action theta e he hc alpha r)
        ((OddDouble.formalShiftFunctor 3).map (FormalSummandAction.action theta e he hc alpha r)) := rfl
end LittleFinitistic.BiprodEvaluationSquare

end

end OAI

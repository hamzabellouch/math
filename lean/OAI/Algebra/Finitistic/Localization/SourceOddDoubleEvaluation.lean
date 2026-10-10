import OAI.Algebra.Finitistic.Localization.SourceCornerEvaluation
import OAI.Algebra.Finitistic.Rectification.BiprodEvaluationSquare

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
private theorem compose_square {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ A) (g : B ⟶ B) (h : D ⟶ D) (e : A ⟶ B) (p : B ⟶ D)
    (he : f ≫ e = e ≫ g) (hp : g ≫ p = p ≫ h) :
    f ≫ (e ≫ p) = (e ≫ p) ≫ h := by
  rw [← Category.assoc, he, Category.assoc, hp, ← Category.assoc]

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

/-- The additive extension respects the native formal shift. -/
def shiftIso (n : ℤ) :
    OddDouble.formalShiftFunctor (C := SourceVerdier.Q E.relations) n ⋙ completed (Y := Y) E ≅
      completed (Y := Y) E ⋙ shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n :=
  completedCommutationIso (evaluation (Y := Y) E) _ _ ((evaluation (Y := Y) E).commShiftIso n)

def shiftedImageIso (e : R) (he : e*e=e) (n : ℤ) :
    (completed (Y := Y) E).obj (OddDouble.formalShift (U E e he) n) ≅
      (imageDerived (k := k) (Y := Y) e)⟦n⟧ :=
  (shiftIso (Y := Y) E n).app (U E e he) ≪≫
    (shiftFunctor _ n).mapIso (summandImageIso (Y := Y) E e he)

theorem shifted_corner_square (e a : R) (he : e*e=e) (n : ℤ) :
    (completed (Y := Y) E).map ((OddDouble.formalShiftFunctor n).map (corner E e a he)) ≫
      (shiftedImageIso (Y := Y) E e he n).hom =
    (shiftedImageIso (Y := Y) E e he n).hom ≫ (imageCorner (k := k) (Y := Y) e a)⟦n⟧' := by
  have hn := (shiftIso (Y := Y) E n).hom.naturality (corner E e a he)
  have hm := congrArg (shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n).map
    (completed_corner_square (Y := Y) E e a he)
  simp only [Functor.map_comp] at hm
  exact compose_square _ _ _ _ _ hn hm

local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _
local instance : PreservesBinaryBiproducts (completed (Y := Y) E) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

def oddDoubleImageIso (e : R) (he : e*e=e) :
    (completed (Y := Y) E).obj (U E e he ⊞ OddDouble.formalShift (U E e he) 3) ≅
      imageDerived (k := k) (Y := Y) e ⊞ (imageDerived (k := k) (Y := Y) e)⟦(3 : ℤ)⟧ :=
  (completed (Y := Y) E).mapBiprod _ _ ≪≫
    biprod.mapIso (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he 3)

theorem oddDouble_corner_square (e a : R) (he : e*e=e) :
    (completed (Y := Y) E).map
      (biprod.map (corner E e a he) ((OddDouble.formalShiftFunctor 3).map (corner E e a he))) ≫
      (oddDoubleImageIso (Y := Y) E e he).hom =
    (oddDoubleImageIso (Y := Y) E e he).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(3 : ℤ)⟧') := by
  exact BiprodEvaluationSquare.square (completed (Y := Y) E)
    (corner E e a he) ((OddDouble.formalShiftFunctor 3).map (corner E e a he))
    (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he 3)
    (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(3 : ℤ)⟧')
    (completed_corner_square E e a he) (shifted_corner_square E e a he 3)

theorem oddDouble_selecting_square (e : R) (he : e*e=e) (hc : ∀ r : R,e*r=r*e)
    (alpha : R →ₐ[k] R) (r : R) :
    (completed (Y := Y) E).map
      (FormalSummandAction.oddDoubleAction (SourceQuotientAction.theta E) e he hc alpha r) ≫
      (oddDoubleImageIso (Y := Y) E e he).hom =
    (oddDoubleImageIso (Y := Y) E e he).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e (alpha r)) ((imageCorner (k := k) (Y := Y) e (alpha r))⟦(3 : ℤ)⟧') := by
  have hc' := selecting_action_eq_corner E e he hc alpha r
  have hd := (BiprodEvaluationSquare.action_formula
    (SourceQuotientAction.theta E) e he hc alpha r).trans
      (congrArg₂ (fun f g => biprod.map f g) hc'
        (congrArg (OddDouble.formalShiftFunctor 3).map hc'))
  exact (congrArg (fun f => (completed (Y := Y) E).map f ≫
    (oddDoubleImageIso (Y := Y) E e he).hom) hd).trans
      (oddDouble_corner_square E e (alpha r) he)
end LittleFinitistic.SourceImageEvaluation

end

end OAI

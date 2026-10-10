import OAI.Algebra.Finitistic.Localization.ModuleActionCompatibility
import OAI.Algebra.Finitistic.Localization.FiniteDerivedEvaluation

namespace OAI
noncomputable section
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

instance finiteUnderlyingLifting : Localization.Lifting
    (boundedDenominators P).Q (boundedDenominators P) (boundedEvaluation X)
    (finiteQuotientEvaluation X ⋙ inclusion k) where
  iso := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteQuotientEvaluationFactors X) (inclusion k)

/-- Both constructions of evaluation through Q agree by uniqueness of localization. -/
def finiteUnderlyingComparison : finiteQuotientEvaluation X ⋙ inclusion k ≅
    boundedQuotientEvaluation X :=
  Localization.liftNatIso (boundedDenominators P).Q (boundedDenominators P)
    (boundedEvaluation X) (boundedEvaluation X) _ _ (Iso.refl _)

/-- The existing finite derived evaluation agrees with canonical derived localization
of the explicitly computed homotopy evaluation. -/
def derivedUnderlyingComparison :
    derivedQuotientEvaluation X ⋙ (derivedEmbedding k).essImage.ι ≅
      boundedQuotientEvaluation X ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerRight (finiteUnderlyingComparison X) DerivedCategory.Qh

def derivedVertexIso (i : Fin 3) :
    ((derivedQuotientEvaluation X ⋙ (derivedEmbedding k).essImage.ι).obj (vertexQ P i)) ≅
      DerivedCategory.Qh.obj ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (derivedUnderlyingComparison X).app (vertexQ P i) ≪≫
    DerivedCategory.Qh.mapIso (quotientVertexIso X i)

/-- The full action square in the actual derived category, for the previously
constructed bounded finite-dimensional evaluation functor. -/
theorem derived_quotientAction_square (r : PresentedAlgebra P) :
    (derivedQuotientEvaluation X ⋙ (derivedEmbedding k).essImage.ι).map (quotientAction P r) ≫
      (derivedVertexIso X 0).hom =
    (derivedVertexIso X 0).hom ≫ DerivedCategory.Qh.map
      ((vectorStalk (k := k)).map (liftedEndHom (givenAction X r))) := by
  have hn := (derivedUnderlyingComparison X).hom.naturality (quotientAction P r)
  have hm := congrArg DerivedCategory.Qh.map (quotientAction_square X r)
  simp only [Functor.map_comp] at hm
  change _ ≫ ((derivedUnderlyingComparison X).hom.app (vertexQ P 0) ≫
    DerivedCategory.Qh.map (quotientVertexIso X 0).hom) =
    ((derivedUnderlyingComparison X).hom.app (vertexQ P 0) ≫
    DerivedCategory.Qh.map (quotientVertexIso X 0).hom) ≫ _
  rw [← Category.assoc, hn, Category.assoc]
  change (derivedUnderlyingComparison X).hom.app (vertexQ P 0) ≫
    (DerivedCategory.Qh.map ((boundedQuotientEvaluation X).map (quotientAction P r)) ≫ _) = _
  rw [hm, ← Category.assoc]
end LittleFinitistic.QuadraticEncoding

end

end OAI

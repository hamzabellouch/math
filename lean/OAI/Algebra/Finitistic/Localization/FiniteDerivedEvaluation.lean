import OAI.Algebra.Finitistic.Localization.FiniteEvaluationTarget
import OAI.Algebra.Finitistic.Localization.BoundedDerivedEmbedding

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

instance finiteQuotientEvaluationAdditive : (finiteQuotientEvaluation X).Additive := by
  rw [Localization.functor_additive_iff (boundedDenominators P).Q (boundedDenominators P)]
  exact Functor.additive_of_iso (finiteQuotientEvaluationFactors X).symm

instance finiteQuotientEvaluationLifting : Localization.Lifting
    (boundedDenominators P).Q (boundedDenominators P)
    (finiteEvaluation X) (finiteQuotientEvaluation X) :=
  ⟨finiteQuotientEvaluationFactors X⟩

instance finiteQuotientEvaluationShift : (finiteQuotientEvaluation X).CommShift ℤ :=
  Functor.commShiftOfLocalization (boundedDenominators P).Q (boundedDenominators P) ℤ
    (finiteEvaluation X) (finiteQuotientEvaluation X)

instance finiteQuotientEvaluationFactorsShift :
    NatTrans.CommShift (finiteQuotientEvaluationFactors X).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Localization.Lifting.iso (boundedDenominators P).Q (boundedDenominators P)
      (finiteEvaluation X) (finiteQuotientEvaluation X)).hom ℤ)

instance finiteQuotientEvaluationTriangulated : (finiteQuotientEvaluation X).IsTriangulated := by
  have : (boundedDenominators P).Q.mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (boundedDenominators P).Q (boundedDenominators P)
  exact Functor.isTriangulated_of_precomp_iso (finiteQuotientEvaluationFactors X)

/-- The full subcategory of the canonical derived category represented by bounded
finite-dimensional complexes. Over a field all its terms are projective. -/
abbrev FiniteVectorDerived := (derivedEmbedding.{u,max u v} k).EssImageSubcategory

instance derivedToEssImageShift : ((derivedEmbedding.{u,max u v} k).toEssImage).CommShift ℤ := by
  dsimp [Functor.toEssImage]
  infer_instance
instance derivedToEssImageTriangulated : ((derivedEmbedding.{u,max u v} k).toEssImage).IsTriangulated := by
  dsimp [Functor.toEssImage]
  infer_instance

def derivedEvaluation : BoundedK P ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  finiteEvaluation X ⋙ (derivedEmbedding k).toEssImage

def derivedQuotientEvaluation : BoundedQ P ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  finiteQuotientEvaluation X ⋙ (derivedEmbedding k).toEssImage

def derivedQuotientEvaluationFactors :
    (boundedDenominators P).Q ⋙ derivedQuotientEvaluation X ≅ derivedEvaluation X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteQuotientEvaluationFactors X) (derivedEmbedding k).toEssImage

instance derivedEvaluationShift : (derivedEvaluation X).CommShift ℤ := by
  dsimp [derivedEvaluation]
  infer_instance
instance derivedEvaluationTriangulated : (derivedEvaluation X).IsTriangulated := by
  dsimp [derivedEvaluation]
  infer_instance
instance derivedQuotientEvaluationShift : (derivedQuotientEvaluation X).CommShift ℤ := by
  dsimp [derivedQuotientEvaluation]
  infer_instance
instance derivedQuotientEvaluationTriangulated :
    (derivedQuotientEvaluation X).IsTriangulated := by
  dsimp [derivedQuotientEvaluation]
  infer_instance
end LittleFinitistic.QuadraticEncoding

end

end OAI

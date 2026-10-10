import OAI.Algebra.Finitistic.Localization.BoundedQuotientEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.QuadraticEncoding
open ThickEvaluation
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The constructed quotient carries its canonical triangulated structure. -/
theorem boundedQ_triangulated : IsTriangulated (BoundedQ P) := inferInstance

variable {P} {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

instance quotientEvaluationAdditive : (boundedQuotientEvaluation X).Additive := by
  rw [Localization.functor_additive_iff (boundedDenominators P).Q (boundedDenominators P)]
  exact Functor.additive_of_iso (boundedQuotientEvaluationFactors X).symm

instance quotientEvaluationLifting : Localization.Lifting
    (boundedDenominators P).Q (boundedDenominators P)
    (boundedEvaluation X) (boundedQuotientEvaluation X) :=
  ⟨boundedQuotientEvaluationFactors X⟩

instance quotientEvaluationShift : (boundedQuotientEvaluation X).CommShift ℤ :=
  Functor.commShiftOfLocalization (boundedDenominators P).Q (boundedDenominators P) ℤ
    (boundedEvaluation X) (boundedQuotientEvaluation X)

instance quotientEvaluationFactorsShift :
    NatTrans.CommShift (boundedQuotientEvaluationFactors X).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Localization.Lifting.iso (boundedDenominators P).Q (boundedDenominators P)
      (boundedEvaluation X) (boundedQuotientEvaluation X)).hom ℤ)

instance quotientEvaluationTriangulated : (boundedQuotientEvaluation X).IsTriangulated := by
  have : (boundedDenominators P).Q.mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (boundedDenominators P).Q (boundedDenominators P)
  exact Functor.isTriangulated_of_precomp_iso (boundedQuotientEvaluationFactors X)
end LittleFinitistic.QuadraticEncoding

end

end OAI

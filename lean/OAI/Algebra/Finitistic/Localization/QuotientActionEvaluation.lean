import OAI.Algebra.Finitistic.Localization.HomotopyVertexEvaluation
import OAI.Algebra.Finitistic.Localization.PresentedQuotientAction

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- The canonical evaluation identification on each vertex of the fixed quotient. -/
def quotientVertexIso (i : Fin 3) :
    (boundedQuotientEvaluation X).obj (vertexQ P i) ≅
      (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (boundedQuotientEvaluationFactors X).app (vertexK P i) ≪≫ homotopyVertexIso X i

lemma quotient_arrow01_square (h : Fin (d+1)) :
    (boundedQuotientEvaluation X).map (arrowQ01 P h) ≫ (quotientVertexIso X 1).hom =
    (quotientVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  have hn := (boundedQuotientEvaluationFactors X).hom.naturality (arrowK01 P h)
  change ((boundedDenominators P).Q ⋙ boundedQuotientEvaluation X).map (arrowK01 P h) ≫
    ((boundedQuotientEvaluationFactors X).hom.app (vertexK P 1) ≫ (homotopyVertexIso X 1).hom) =
    ((boundedQuotientEvaluationFactors X).hom.app (vertexK P 0) ≫ (homotopyVertexIso X 0).hom) ≫ _
  rw [← Category.assoc, hn, Category.assoc, homotopy_arrow01_square, ← Category.assoc]

lemma quotient_arrow12_square (h : Fin (d+1)) :
    (boundedQuotientEvaluation X).map (arrowQ12 P h) ≫ (quotientVertexIso X 2).hom =
    (quotientVertexIso X 1).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  have hn := (boundedQuotientEvaluationFactors X).hom.naturality (arrowK12 P h)
  change ((boundedDenominators P).Q ⋙ boundedQuotientEvaluation X).map (arrowK12 P h) ≫
    ((boundedQuotientEvaluationFactors X).hom.app (vertexK P 2) ≫ (homotopyVertexIso X 2).hom) =
    ((boundedQuotientEvaluationFactors X).hom.app (vertexK P 1) ≫ (homotopyVertexIso X 1).hom) ≫ _
  rw [← Category.assoc, hn, Category.assoc, homotopy_arrow12_square, ← Category.assoc]

@[simp] lemma actionArrow_zero : actionArrow X 0 = 𝟙 _ := by ext y; rfl

lemma quotient_inverse_s_square :
    (boundedQuotientEvaluation X).map (inv (arrowQ01 P 0)) ≫ (quotientVertexIso X 0).hom =
      (quotientVertexIso X 1).hom := by
  apply (cancel_epi ((boundedQuotientEvaluation X).map (arrowQ01 P 0))).mp
  simp only [← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
  symm
  simpa using quotient_arrow01_square X 0

/-- The normalized quotient generator evaluates to the given generator on Y. -/
theorem normalizedGenerator_evaluates (h : Fin d) :
    (boundedQuotientEvaluation X).map (normalizedGenerator P h) ≫ (quotientVertexIso X 0).hom =
      (quotientVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X h.succ) := by
  simp only [normalizedGenerator, Functor.map_comp, Category.assoc]
  rw [quotient_inverse_s_square, quotient_arrow01_square]
end LittleFinitistic.QuadraticEncoding

end

end OAI

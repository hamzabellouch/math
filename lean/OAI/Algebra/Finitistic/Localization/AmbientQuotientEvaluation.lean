import OAI.Algebra.Finitistic.Selected.SelectedVertexTensorEvaluation
import OAI.Algebra.Finitistic.Localization.HomotopyEvaluation
import OAI.Algebra.Finitistic.Localization.ThickEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic
open BalancedTensor ThickEvaluation
universe u v
namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The ambient homotopy category; no bounded-projective identification is asserted here. -/
abbrev Ambient := HomotopyCategory (ModuleCat.{u} (B P)ᵐᵒᵖ) (ComplexShape.up ℤ)

def degreeZero := HomologicalComplex.single (ModuleCat.{u} (B P)ᵐᵒᵖ) (ComplexShape.up ℤ) (0 : ℤ)
def coneS : Ambient P := (HomotopyCategory.quotient _ _).obj
  (CochainComplex.mappingCone ((degreeZero P).map (arrowModule01 P 0)))
def coneS' : Ambient P := (HomotopyCategory.quotient _ _).obj
  (CochainComplex.mappingCone ((degreeZero P).map (arrowModule12 P 0)))

def coneGenerators : ObjectProperty (Ambient P) := fun T => T = coneS P ∨ T = coneS' P

def ambientDenominators : MorphismProperty (Ambient P) :=
  ObjectProperty.trW (Thick (coneGenerators P))

/-- A quotient fixed before Y is chosen, for the ambient homotopy category. -/
abbrev AmbientQuotient := (ambientDenominators P).Localization

variable {P} {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

lemma eval_single_isIso {M M' : ModuleCat.{u} (B P)ᵐᵒᵖ} (f : M ⟶ M')
    [IsIso ((tensorFunctor k (B P) X.Evaluation).map f)] :
    IsIso ((homotopyEvaluation k (B P) X.Evaluation).map
      ((HomotopyCategory.quotient _ _).map ((degreeZero P).map f))) := by
  let F := tensorFunctor k (B P) X.Evaluation
  have h : IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ((degreeZero P).map f)) := by
    exact (NatIso.isIso_map_iff
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) (0 : ℤ)) f).mpr
      (by
        change IsIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map
          ((tensorFunctor k (B P) X.Evaluation).map f))
        infer_instance)
  change IsIso ((HomotopyCategory.quotient _ _).map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ((degreeZero P).map f)))
  infer_instance

lemma evaluation_coneS_zero : IsZero ((homotopyEvaluation k (B P) X.Evaluation).obj (coneS P)) := by
  have := evaluation_s_isIso X
  have := eval_single_isIso X (arrowModule01 P 0)
  exact Triangle.isZero₃_of_isIso₁ _
    ((homotopyEvaluation k (B P) X.Evaluation).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished ((degreeZero P).map (arrowModule01 P 0))))
    (inferInstanceAs (IsIso ((homotopyEvaluation k (B P) X.Evaluation).map
      ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P 0))))))

lemma evaluation_coneS'_zero : IsZero ((homotopyEvaluation k (B P) X.Evaluation).obj (coneS' P)) := by
  have := evaluation_s'_isIso X
  have := eval_single_isIso X (arrowModule12 P 0)
  exact Triangle.isZero₃_of_isIso₁ _
    ((homotopyEvaluation k (B P) X.Evaluation).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished ((degreeZero P).map (arrowModule12 P 0))))
    (inferInstanceAs (IsIso ((homotopyEvaluation k (B P) X.Evaluation).map
      ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P 0))))))

lemma kills_coneGenerators : ∀ T, coneGenerators P T →
    IsZero ((homotopyEvaluation k (B P) X.Evaluation).obj T) := by
  rintro T (rfl | rfl)
  · exact evaluation_coneS_zero X
  · exact evaluation_coneS'_zero X

/-- Actual tensor evaluation on the ambient quotient, with the generator hypotheses proved. -/
def ambientQuotientEvaluation : AmbientQuotient P ⥤
    HomotopyCategory (ModuleCat.{max u v} k) (ComplexShape.up ℤ) :=
  quotientEvaluation (coneGenerators P) (homotopyEvaluation k (B P) X.Evaluation)
    (kills_coneGenerators X)

def ambientQuotientEvaluationFactors :
    (ambientDenominators P).Q ⋙ ambientQuotientEvaluation X ≅
      homotopyEvaluation k (B P) X.Evaluation :=
  quotientEvaluationFactors (coneGenerators P) (homotopyEvaluation k (B P) X.Evaluation)
    (kills_coneGenerators X)
end QuadraticEncoding
end LittleFinitistic

end

end OAI

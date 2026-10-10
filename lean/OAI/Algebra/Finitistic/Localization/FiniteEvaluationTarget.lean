import OAI.Algebra.Finitistic.Localization.LocalizedEvaluationStructure

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy ThickEvaluation
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

/-- The concrete bounded homotopy category of finite-dimensional vector spaces. -/
abbrev FiniteVectorHomotopy := K.{u,max u v} k

theorem finiteEvaluation_property (T : BoundedK P) :
    objects k ((boundedEvaluation X).obj T) := by
  obtain ⟨hb,hf⟩ := boundedEvaluation_finite X T
  refine ⟨hb,fun i => ⟨hf i,?_⟩⟩
  exact ModuleCat.projective_of_categoryTheory_projective _

/-- Evaluation with bounded finite-dimensional vector-space complexes as its actual target. -/
def finiteEvaluation : BoundedK P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  (objects k).lift (boundedEvaluation X) (finiteEvaluation_property X)

instance finiteEvaluationAdditive : (finiteEvaluation X).Additive := by
  dsimp [finiteEvaluation]
  infer_instance
instance finiteEvaluationShift : (finiteEvaluation X).CommShift ℤ := by
  dsimp [finiteEvaluation]
  infer_instance
instance finiteEvaluationTriangulated : (finiteEvaluation X).IsTriangulated := by
  dsimp [finiteEvaluation]
  infer_instance

lemma finiteEvaluation_kills_generators : ∀ T, boundedConeGenerators P T →
    IsZero ((finiteEvaluation X).obj T) := by
  intro T hT
  apply IsZero.of_full_of_faithful_of_isZero (inclusion k)
  exact boundedEvaluation_kills_generators X T hT

/-- The fixed quotient Q evaluates directly into bounded finite-dimensional complexes. -/
def finiteQuotientEvaluation : BoundedQ P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  quotientEvaluation (boundedConeGenerators P) (finiteEvaluation X)
    (finiteEvaluation_kills_generators X)

def finiteQuotientEvaluationFactors :
    (boundedDenominators P).Q ⋙ finiteQuotientEvaluation X ≅ finiteEvaluation X :=
  quotientEvaluationFactors (boundedConeGenerators P) (finiteEvaluation X)
    (finiteEvaluation_kills_generators X)
end LittleFinitistic.QuadraticEncoding

end

end OAI

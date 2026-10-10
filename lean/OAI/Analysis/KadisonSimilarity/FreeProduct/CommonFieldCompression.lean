import OAI.Analysis.KadisonSimilarity.Representation.CommonSpectralCommutant
import OAI.Analysis.KadisonSimilarity.Representation.ContinuousFieldCommutation
import OAI.Analysis.KadisonSimilarity.Representation.SupportedFieldRecovery

namespace OAI

/-! Compressing an actual measurable field in the common spectral model
returns an operator in the original abelian commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- The original operator obtained by compressing the reconstructed field. -/
def commonFieldCompression
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) : H →L[ℂ] H :=
  ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
    (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap

/-- Expose the compression formula without unfolding its field operator. -/
theorem commonFieldCompression_eq
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    commonFieldCompression π D R hmeas C hbound =
      ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
        (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
          (cyclicCommonEmbedding π D).toContinuousLinearMap := rfl

theorem commonFieldCompression_mem
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    commonFieldCompression π D R hmeas C hbound ∈ starSubalgebraCommutant π.range := by
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
  rintro _ ⟨a, rfl⟩
  apply Eq.symm
  apply commonCompression_commutes_representation π D
  intro b
  rw [commonScalarRepresentation_apply]
  exact boundedFieldOperator_commutes_continuous (cyclicCommonBaseMeasure π D)
    R hmeas C hbound (gelfandStarTransform A b)

/-- The same compression belongs to any representation generating this
commutant. -/
theorem commonFieldCompression_mem_of_range_eq {B : Type*} [CStarAlgebra B]
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra σ = starSubalgebraCommutant π.range)
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
      (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
        (cyclicCommonEmbedding π D).toContinuousLinearMap ∈
      representationVonNeumannAlgebra σ := by
  have h := hgen.ge (commonFieldCompression_mem π D R hmeas C hbound)
  rw [commonFieldCompression_eq] at h
  exact h

end KadisonSimilarity

end

end OAI

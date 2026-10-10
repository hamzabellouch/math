import OAI.Analysis.KadisonSimilarity.Representation.BoundedMeasurableField
import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension
import OAI.Analysis.KadisonSimilarity.Representation.ProjectionRankOne

namespace OAI

/-! Supported measurable fields are recovered exactly by compression to the
original Hilbert space. In particular, the supported rank-one tests used for
factor fibers come from actual original operators. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω H F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure Ω) (J : H →ₗᵢ[ℂ] Lp F 2 μ)

/-- An operator field supported on the original range is exactly the
zero extension of its compression. -/
theorem isometricExtension_boundedField_compression
    (p R : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (hmeas : ∀ v : F, AEStronglyMeasurable (fun x => R x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ C)
    (hleft : ∀ᵐ x ∂μ, p x * R x = R x)
    (hright : ∀ᵐ x ∂μ, R x * p x = R x) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hmeas C hbound)).comp
        J.toContinuousLinearMap) = boundedFieldOperator μ R hmeas C hbound :=
  isometricExtension_compression J _
    (boundedFieldOperator_left_support μ R hmeas C hbound _ p hP hleft)
    (boundedFieldOperator_right_support μ R hmeas C hbound _ p hP hright)

variable [IsFiniteMeasure μ]

/-- The projection columns of the original range are strongly measurable. -/
theorem aestronglyMeasurable_isometric_projection_column
    (p : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (v : F) : AEStronglyMeasurable (fun x => p x v) μ :=
  (Lp.aestronglyMeasurable (isometricExtension J 1 (Lp.const 2 μ v))).congr
    (pointwise_action_column μ _ p hP v)

/-- Every supported rank-one field is the field of an actual operator on
the original Hilbert space. -/
theorem exists_isometric_projection_rankOne_field
    (p : Ω → F →L[ℂ] F) (hp : ∀ x, IsStarProjection (p x))
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (v w : F) :
    ∃ T : H →L[ℂ] H, ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x =
        InnerProductSpace.rankOne ℂ (p x v) (p x w) (f x) := by
  let R : Ω → F →L[ℂ] F := fun x => InnerProductSpace.rankOne ℂ (p x v) (p x w)
  have hm : ∀ z : F, AEStronglyMeasurable (fun x => R x z) μ :=
    aestronglyMeasurable_projection_rankOne μ p
      (aestronglyMeasurable_isometric_projection_column μ J p hP) v w
  have hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ ‖v‖ * ‖w‖ :=
    Filter.Eventually.of_forall fun x => norm_projection_rankOne_le (p x) (hp x) v w
  let Q := boundedFieldOperator μ R hm (‖v‖ * ‖w‖) hb
  refine ⟨(J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap, ?_⟩
  have he := isometricExtension_boundedField_compression μ J p R hP hm _ hb
    (Filter.Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).1)
    (Filter.Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).2)
  intro f
  rw [he]
  exact boundedFieldOperator_action μ R hm _ hb f

end KadisonSimilarity

end

end OAI

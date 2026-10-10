import OAI.Analysis.IrrationalRotation.Operators.FieldOperator
import OAI.Analysis.IrrationalRotation.Analysis.StrongFieldMeasurability

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SeparableSpace E]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem ae_isIdempotentElem_of_fieldOperator (hC : 0 ≤ C)
    (hP : IsIdempotentElem (fieldOperator A C hA hm)) :
    ∀ᵐ x ∂μ, IsIdempotentElem (A x) := by
  have hAA : ∀ x, ‖A x * A x‖ ≤ C * C := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul (hA x) (hA x) (norm_nonneg _) hC)
  have hmAA : ∀ v, AEStronglyMeasurable (fun x => (A x * A x) v) μ := fun v =>
    apply_aestronglyMeasurable A hm (hm v)
  have hmul : fieldOperator (fun x => A x * A x) (C * C) hAA hmAA =
      fieldOperator A C hA hm * fieldOperator A C hA hm :=
    fieldOperator_comp_of_ae_eq (Filter.Eventually.of_forall fun x => rfl)
  have hfield := fieldOperator_ae_eq_of_eq (hmul.trans hP.eq)
  exact hfield

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeparableSpace E] [Countable ι]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}

theorem ae_isSelfAdjoint_of_fieldOperator (b : HilbertBasis ι ℂ E)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsSelfAdjoint (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsSelfAdjoint (A x) := by
  have hB : ∀ x, ‖star (A x)‖ ≤ C := by
    intro x
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact hA x
  have hn : ∀ v, AEStronglyMeasurable (fun x => star (A x) v) μ := by
    intro v
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (StrongField.stronglyMeasurable_adjoint_apply_of_columns b A
        (fun i => hm (b i)) v).aestronglyMeasurable
  have hglobal : fieldOperator (fun x => star (A x)) C hB hn =
      star (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable)) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact fieldOperator_adjoint_of_ae_eq (Filter.Eventually.of_forall fun x =>
      ContinuousLinearMap.star_eq_adjoint (A x))
  exact fieldOperator_ae_eq_of_eq (hglobal.trans hP.star_eq)

theorem ae_isStarProjection_of_fieldOperator (b : HilbertBasis ι ℂ E) (hC : 0 ≤ C)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsStarProjection (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsStarProjection (A x) := by
  filter_upwards [ae_isIdempotentElem_of_fieldOperator hC hP.isIdempotentElem,
    ae_isSelfAdjoint_of_fieldOperator b hm hP.isSelfAdjoint] with x hid hself
  exact ⟨hid, hself⟩

end Invariant233.DirectIntegral

end

end OAI

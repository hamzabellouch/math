import OAI.Analysis.KadisonKastler.TomiyamaDenseProjections
import OAI.Analysis.KadisonKastler.WeakFieldProjectionDensity
import OAI.Analysis.KadisonKastler.PublishedFieldTomiyama

namespace OAI

/-! # Tomiyama's bimodule identity for measurable operator fields

The measurable representative algebra has norm-dense projection span, by
the pointwise spectral construction. This property descends through its
quotient map. The projection identities for contractive retractions
therefore give the field version of Tomiyama's theorem.
-/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm-density of projection spans passes to the field quotient. -/
theorem weakOperatorField_closed_projection_span_eq_top :
    (Submodule.span ℂ {p : WeakOperatorField (H := H) μ |
      IsStarProjection p}).topologicalClosure = ⊤ := by
  exact closed_projection_span_eq_top_of_surjective (operatorFieldQuotient (H := H) μ)
    (operatorFieldQuotient_surjective (H := H) μ)
    (WeakOperatorRepresentative.closed_projection_span_eq_top (H := H) (μ := μ))

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasureTheory.IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [Group G] [DiscreteTopology G] [MeasureTheory.IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
/-- The constant-field specialization of Tomiyama's theorem is proved
from the C-star norm geometry and measurable spectral projections. -/
theorem publishedFieldTomiyama : PublishedFieldTomiyama (G := G) (H := H) (μ := μ) := by
  intro E hE hfix
  exact tomiyama_map_mul_of_dense_projections
    (weakOperatorField_closed_projection_span_eq_top (H := H) (μ := μ))
    (operatorFieldDiagonal (G := G) (H := H) (μ := μ)) E hE hfix

end

end KadisonKastler

end OAI

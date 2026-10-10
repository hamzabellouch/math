import OAI.Analysis.KadisonSimilarity.Representation.BoundedMeasurableField
import OAI.Analysis.KadisonSimilarity.Representation.VectorL2Representation

namespace OAI

/-! Every bounded measurable operator field commutes with continuous scalar
multiplication, directly from its action on L² sections. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω H : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem boundedFieldOperator_commutes_continuous
    (R : Ω → H →L[ℂ] H)
    (hmeas : ∀ v : H, AEStronglyMeasurable (fun a => R a v) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : C(Ω, ℂ)) :
    boundedFieldOperator μ R hmeas C hbound * VectorL2.continuousL2Mul μ f =
      VectorL2.continuousL2Mul μ f * boundedFieldOperator μ R hmeas C hbound := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [boundedFieldOperator_action μ R hmeas C hbound
      (VectorL2.continuousL2Mul μ f ξ),
    boundedFieldOperator_action μ R hmeas C hbound ξ,
    VectorL2.continuousL2Mul_ae μ f ξ,
    VectorL2.continuousL2Mul_ae μ f (boundedFieldOperator μ R hmeas C hbound ξ)]
    with a hRm hR hm hmr
  change boundedFieldOperator μ R hmeas C hbound (VectorL2.continuousL2Mul μ f ξ) a =
    VectorL2.continuousL2Mul μ f (boundedFieldOperator μ R hmeas C hbound ξ) a
  rw [hRm, hmr, hm, hR, map_smul]

end KadisonSimilarity

end

end OAI

import OAI.Analysis.KadisonKastler.OperatorCoefficientMean
import OAI.Analysis.KadisonKastler.ScalarMeanStar

namespace OAI

/-! # Adjoint preservation of operator-field averaging -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

theorem coefficient_star (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient (star F) ξ η = star (coefficient F η ξ) := by
  apply Lp.ext
  filter_upwards [coefficient_ae (star F) ξ η, coefficient_ae F η ξ,
    Lp.coeFn_star (coefficient F η ξ)] with x ha hb hs
  simp only [Pi.star_apply] at hs
  rw [ha, hs, hb, eval_star]
  change inner ℂ η ((eval F x).adjoint ξ) = star (inner ℂ ξ (eval F x η))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

end WeakOperatorRepresentative

namespace WeakOperatorField

theorem coefficient_star (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (star T) ξ η = star (coefficient T η ξ) := by
  rw [← quotient_representative T, ← map_star, coefficient_quotient,
    coefficient_quotient, WeakOperatorRepresentative.coefficient_star]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_star (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (star F) ξ η = scalarBoundaryStar (coefficientFamily F η ξ) := by
  apply BoundedContinuousFunction.ext
  intro g
  simp only [coefficientFamily_apply, scalarBoundaryStar_apply,
    BoundedContinuousFunction.star_apply, coefficient_star]

end WeakOperatorField

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]
  {α : NonsingularAction G D μ}

namespace ScalarBoundaryMean

/-- Adjoint preservation is derived from scalar positivity. -/
theorem operatorMean_star (m : ScalarBoundaryMean α) (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMean (star F) = star (m.operatorMean F) := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [WeakOperatorField.coefficient_star, operatorMean_apply, operatorMean_apply,
    m.operatorMeanValue_coefficient, m.operatorMeanValue_coefficient,
    WeakOperatorField.coefficientFamily_star, m.map_star]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI

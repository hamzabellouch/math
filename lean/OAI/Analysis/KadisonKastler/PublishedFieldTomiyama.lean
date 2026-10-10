import OAI.Analysis.KadisonKastler.OperatorMeanStar

namespace OAI

/-! # The precise Tomiyama input for the operator-field mean

Tomiyama, *On the projection of norm one in W*-algebras*, Proceedings of
 the Japan Academy 33 (1957), 608–612, Theorem 1(2), pp. 608–609,
 DOI 10.3792/pja/1195524885.

Only the bimodule conclusion for the constant-field inclusion is retained.
The contractive retraction and its adjoint preservation are constructed in
`OperatorCoefficientMean` and `OperatorMeanStar`, not assumed here.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : MeasureTheory.Measure D} [MeasureTheory.IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

instance operatorFieldFamilyCStar : CStarAlgebra (G →ᵇ WeakOperatorField (H := H) μ) where

/-- Constant fields form the target C-star subalgebra of the expectation. -/
abbrev operatorFieldDiagonal : WeakOperatorField (H := H) μ →⋆ₐ[ℂ]
    (G →ᵇ WeakOperatorField (H := H) μ) := boundaryConstant

/-- The constant-field specialization of Tomiyama's Theorem 1(2).
This is an explicit published-input hypothesis, not an axiom. -/
def PublishedFieldTomiyama : Prop :=
  ∀ E : (G →ᵇ WeakOperatorField (H := H) μ) →L[ℂ] WeakOperatorField (H := H) μ,
    (∀ F, ‖E F‖ ≤ ‖F‖) →
    (∀ T, E (operatorFieldDiagonal T) = T) →
    (∀ T F, E (operatorFieldDiagonal T * F) = T * E F) ∧
      (∀ F T, E (F * operatorFieldDiagonal T) = E F * T)

namespace ScalarBoundaryMean

variable {α : NonsingularAction G D μ}

/-- The constructed scalar-coefficient mean is bimodular conditionally only
on the indicated published projection theorem. -/
def operatorBimoduleMean (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ)) :
    BimoduleMean (operatorFieldDiagonal (G := G) (H := H) (μ := μ)) where
  toCLM := m.operatorMean
  map_one := m.operatorMean_fixed 1
  map_star := m.operatorMean_star
  norm_le := m.norm_operatorMeanValue_le
  map_left := (hTom m.operatorMean m.norm_operatorMeanValue_le m.operatorMean_fixed).1
  map_right := (hTom m.operatorMean m.norm_operatorMeanValue_le m.operatorMean_fixed).2

end ScalarBoundaryMean

end

end KadisonKastler

end OAI

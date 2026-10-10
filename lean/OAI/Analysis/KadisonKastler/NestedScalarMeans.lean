import OAI.Analysis.KadisonKastler.BoundedFamilyCurry
import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # Composing scalar means over two group coordinates

The row and outer means are bounded linear maps on actual L-infinity classes.
Here we establish the algebraic and norm properties of their composition;
the action identity is supplied by the commuting-coordinate construction.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]
  {α β : NonsingularAction G D μ}

def nestedMeanRowsL (m : ScalarBoundaryMean β) :
    ((G × G) →ᵇ ScalarLInfinity μ) →L[ℂ] (G →ᵇ ScalarLInfinity μ) :=
  (m.toCLM.compLeftContinuousBounded G).comp boundedFamilyCurryL

@[simp]
theorem nestedMeanRowsL_apply (m : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) (g : G) :
    nestedMeanRowsL m F g = m.toCLM (boundedFamilyRow F g) := rfl

def nestedScalarMeanL (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β) :
    ((G × G) →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ :=
  m₁.toCLM.comp (nestedMeanRowsL m₂)

theorem nestedMeanRowsL_norm_le (m : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) : ‖nestedMeanRowsL m F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  exact (m.norm_le _).trans (boundedFamilyRow_norm_le F g)

theorem nestedScalarMeanL_norm_le (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ) : ‖nestedScalarMeanL m₁ m₂ F‖ ≤ ‖F‖ :=
  (m₁.norm_le _).trans (nestedMeanRowsL_norm_le m₂ F)

theorem nestedMeanRowsL_const (m : ScalarBoundaryMean β) (b : ScalarLInfinity μ) :
    nestedMeanRowsL m (BoundedContinuousFunction.const (G × G) b) =
      BoundedContinuousFunction.const G b := by
  apply BoundedContinuousFunction.ext
  intro g
  exact m.fixed b

theorem nestedScalarMeanL_const (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (b : ScalarLInfinity μ) :
    nestedScalarMeanL m₁ m₂ (BoundedContinuousFunction.const (G × G) b) = b := by
  change m₁.toCLM (nestedMeanRowsL m₂ _) = b
  rw [nestedMeanRowsL_const, m₁.fixed]

theorem nestedScalarMeanL_positive (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (F : (G × G) →ᵇ ScalarLInfinity μ)
    (hF : ∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) :
    ∀ᵐ x ∂μ, (nestedScalarMeanL m₁ m₂ F x).im = 0 ∧
      0 ≤ (nestedScalarMeanL m₁ m₂ F x).re := by
  apply m₁.positive
  intro g
  exact m₂.positive (boundedFamilyRow F g) (fun h => hF (g, h))

theorem nestedMeanRowsL_module (m : ScalarBoundaryMean β) (b : ScalarLInfinity μ)
    (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedMeanRowsL m (scalarBoundaryModule b F) = scalarBoundaryModule b (nestedMeanRowsL m F) := by
  apply BoundedContinuousFunction.ext
  intro g
  have hr : boundedFamilyRow (scalarBoundaryModule b F) g =
      scalarBoundaryModule b (boundedFamilyRow F g) := by
    apply BoundedContinuousFunction.ext
    intro h
    rfl
  change m.toCLM (boundedFamilyRow (scalarBoundaryModule b F) g) = _
  rw [hr, m.module_map]
  rfl

theorem nestedScalarMeanL_module (m₁ : ScalarBoundaryMean α) (m₂ : ScalarBoundaryMean β)
    (b : ScalarLInfinity μ) (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedScalarMeanL m₁ m₂ (scalarBoundaryModule b F) =
      scalarInfinityMul b (nestedScalarMeanL m₁ m₂ F) := by
  change m₁.toCLM (nestedMeanRowsL m₂ (scalarBoundaryModule b F)) = _
  rw [nestedMeanRowsL_module, m₁.module_map]
  rfl

end

end KadisonKastler

end OAI

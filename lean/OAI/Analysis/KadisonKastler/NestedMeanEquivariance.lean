import OAI.Analysis.KadisonKastler.NestedScalarMeans
import OAI.Analysis.KadisonKastler.ScalarPullbackAlgebra

namespace OAI

/-! # Equivariance of nested means for separate group actions -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]
  (α₁ α₂ : NonsingularAction G D μ) (β : NonsingularAction (G × G) D μ)
  (hβ : ∀ g z, β.toPerm g z = α₁.toPerm g.1 (α₂.toPerm g.2 z))

include hβ in
omit [TopologicalSpace G] [DiscreteTopology G] [IsProbabilityMeasure μ] in
theorem scalarSeparatePullback (g : G × G) (f : ScalarLInfinity μ) :
    scalarInfinityPullback (β.toPerm g) (β.quasi g) f =
      scalarInfinityPullback (α₂.toPerm g.2) (α₂.quasi g.2)
        (scalarInfinityPullback (α₁.toPerm g.1) (α₁.quasi g.1) f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae (β.toPerm g) (β.quasi g) f,
    scalarInfinityPullback_ae (α₂.toPerm g.2) (α₂.quasi g.2)
      (scalarInfinityPullback (α₁.toPerm g.1) (α₁.quasi g.1) f),
    (α₂.quasi g.2).ae (scalarInfinityPullback_ae (α₁.toPerm g.1) (α₁.quasi g.1) f)]
    with z ha hb hc
  rw [ha, hb, hc, hβ]

variable (m₁ : ScalarBoundaryMean α₁) (m₂ : ScalarBoundaryMean α₂)
  (hn₁ : ∀ g F, m₁.toCLM
    ((scalarInfinityPullbackL (α₂.toPerm g) (α₂.quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (α₂.toPerm g) (α₂.quasi g) (m₁.toCLM F))
  (hn₂ : ∀ g F, m₂.toCLM
    ((scalarInfinityPullbackL (α₁.toPerm g) (α₁.quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (α₁.toPerm g) (α₁.quasi g) (m₂.toCLM F))

include hβ hn₁ hn₂ in
theorem nestedScalarMeanL_equivariant (g : G × G)
    (F : (G × G) →ᵇ ScalarLInfinity μ) :
    nestedScalarMeanL m₁ m₂ (scalarBoundaryTranslate β g F) =
      scalarInfinityPullback (β.toPerm g⁻¹) (β.quasi g⁻¹) (nestedScalarMeanL m₁ m₂ F) := by
  have hrow (t : G) : boundedFamilyRow (scalarBoundaryTranslate β g F) t =
      scalarBoundaryTranslate α₂ g.2
        ((scalarInfinityPullbackL (α₁.toPerm g.1⁻¹) (α₁.quasi g.1⁻¹)).compLeftContinuousBounded G
          (boundedFamilyRow F (g.1⁻¹ * t))) := by
    apply BoundedContinuousFunction.ext
    intro s
    exact scalarSeparatePullback α₁ α₂ β hβ g⁻¹ (F (g.1⁻¹ * t, g.2⁻¹ * s))
  have hrows : nestedMeanRowsL m₂ (scalarBoundaryTranslate β g F) =
      (scalarInfinityPullbackL (α₂.toPerm g.2⁻¹) (α₂.quasi g.2⁻¹)).compLeftContinuousBounded G
        (scalarBoundaryTranslate α₁ g.1 (nestedMeanRowsL m₂ F)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change m₂.toCLM (boundedFamilyRow (scalarBoundaryTranslate β g F) t) = _
    rw [hrow, m₂.equivariant, hn₂]
    rfl
  change m₁.toCLM (nestedMeanRowsL m₂ (scalarBoundaryTranslate β g F)) = _
  rw [hrows, hn₁, m₁.equivariant]
  exact (scalarSeparatePullback α₁ α₂ β hβ g⁻¹ (nestedScalarMeanL m₁ m₂ F)).symm

def nestedScalarBoundaryMean : ScalarBoundaryMean β where
  toCLM := nestedScalarMeanL m₁ m₂
  map_one := nestedScalarMeanL_const m₁ m₂ _
  norm_le := nestedScalarMeanL_norm_le m₁ m₂
  positive := nestedScalarMeanL_positive m₁ m₂
  module_map := nestedScalarMeanL_module m₁ m₂
  equivariant := nestedScalarMeanL_equivariant α₁ α₂ β hβ m₁ m₂ hn₁ hn₂

end

end KadisonKastler

end OAI

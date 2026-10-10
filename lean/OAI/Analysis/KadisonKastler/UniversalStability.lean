import OAI.Analysis.KadisonKastler.UnitaryBorelSelection
import OAI.Analysis.KadisonKastler.InfiniteFactorStability
import OAI.Analysis.KadisonKastler.FactorStability

namespace OAI

/-! # Universal strong stability from perturbation and decomposition theorems

The factor case split and central decomposition extend the fixed-factor
perturbation estimates to arbitrary representations.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance universalStabilityOrder {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance universalStabilityStarOrder {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- Perturbation and decomposition hypotheses for universal strong stability,
including type I injectivity, infinite-factor projection structure,
central decomposition, and Dixmier averaging. -/
structure UniversalStabilityPublishedInputs : Prop extends FixedFactorPublishedInputs.{u} where
  typeI : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
    PublishedTypeIInjectivity (H := H)
  infiniteType : PublishedInfiniteFactorProperlyInfinite.{u}
  central : PublishedCentralPairDecomposition.{u}
  dixmier : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H), PublishedDixmierAveraging P

/-- The factor conclusion follows from the constructed properly infinite
case and the type I/finite case split. -/
theorem uniform_factor_strong_stability_of_published
    (h : UniversalStabilityPublishedInputs.{u}) : UniformFactorStability.{u} :=
  uniformFactorStability_of_properlyInfinite
    (uniform_properlyInfinite_strong_stability h.toFixedFactorPublishedInputs)
    h.finite h.typeI h.infiniteType

/-- Universal strong Kadison--Kastler stability, with its tolerance chosen
before all Hilbert spaces and represented von Neumann algebras, under the
perturbation and decomposition hypotheses. -/
theorem universal_strong_stability_of_published
    (h : UniversalStabilityPublishedInputs.{u}) : UniversalStrongStability.{u} :=
  universalStrongStability_of_factors
    (uniform_factor_strong_stability_of_published h)
    h.central h.kaplansky publishedUnitaryBorelSelection h.dixmier
    h.correction (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)

end

end KadisonKastler

end OAI

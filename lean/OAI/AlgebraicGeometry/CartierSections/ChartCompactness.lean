/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license.
Authors: OpenAI
-/
import OAI.AlgebraicGeometry.CartierSections.FieldTopology
import OAI.AlgebraicGeometry.CartierSections.FieldRetraction

namespace OAI

/-!
# Compactness of monomial retractions on a closed étale chart

Local algebra for uniform Cartier sections.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace CartierSections
section ClosedChartFieldTopology
universe u
local instance polynomialOrigin_isMaximal_topology {σ k : Type u} [Fintype σ] [Field k] :
    (MvPolynomial.idealOfVars σ k).IsMaximal :=
  polynomialOrigin_isMaximal

variable {σ k R A K : Type u} [Fintype σ] [Field k] [IsAlgClosed k]
  [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) A]
  [Algebra k A] [IsScalarTower k (MvPolynomial σ k) A]
  [Algebra R A] [IsScalarTower (MvPolynomial σ k) R A]
  [IsLocalization.AtPrime R (MvPolynomial.idealOfVars σ k)]
  [IsLocalHom (algebraMap R A)] [Algebra.FormallyUnramified R A]
  [Algebra.EssFiniteType R A] [Algebra.FormallyEtale (MvPolynomial σ k) A]

/-- Monomial retractions of a closed étale chart vary continuously with the weights. -/
lemma continuous_closedChartFieldRetraction_evaluations :
    Continuous (fun w : σ → NNReal => fun x : K =>
      closedChartFieldRetraction (σ := σ) (k := k) (R := R) (A := A) w x) :=
  continuous_expandedFractionValuation_evaluations
    (closedChartExpansion (σ := σ) (k := k) (R := R) (A := A))
    (closedChartExpansion_injective (σ := σ) (k := k) (R := R) (A := A))

/-- The normalized monomial retractions on the fraction field of a closed étale
chart form a compact set in the topology of pointwise evaluation. -/
lemma isCompact_closedChartFieldRetraction_cone
    (a : σ → NNReal) (ha : ∀ i, 0 < a i) :
    IsCompact ((fun w : σ → NNReal => fun x : K =>
      closedChartFieldRetraction (σ := σ) (k := k) (R := R) (A := A) w x) ''
      normalizedWeights a) :=
  (isCompact_normalizedWeights a ha).image
    (continuous_closedChartFieldRetraction_evaluations
      (σ := σ) (k := k) (R := R) (A := A) (K := K))

end ClosedChartFieldTopology
end CartierSections

end

end OAI

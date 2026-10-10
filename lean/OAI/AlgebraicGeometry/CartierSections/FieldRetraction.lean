import OAI.AlgebraicGeometry.CartierSections.ChartRetraction
import OAI.AlgebraicGeometry.CartierSections.FractionValuation

namespace OAI

/-!
# Monomial retractions on rational function fields

The closed étale chart retraction extends to the chart's fraction field.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections
section ClosedRetractionField
universe u
local instance polynomialOrigin_isMaximal_field {σ k : Type u} [Fintype σ] [Field k] :
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

/-- The retraction is a valuation of the chart's actual rational function field. -/
noncomputable def closedChartFieldRetraction (w : σ → NNReal) : AddValuation K (WithTop ℝ) :=
  fractionValuation (closedChartRetraction (σ := σ) (k := k) (A := A) (R := R) w)
    (fun _ hf => (closedChartRetraction_finite (σ := σ) (k := k) (A := A) (R := R) w hf).ne)

@[simp] lemma closedChartFieldRetraction_regular (w : σ → NNReal) (f : A) :
    closedChartFieldRetraction (σ := σ) (k := k) (R := R) (A := A) (K := K) w (algebraMap A K f) =
      nonnegToExtendedReal (closedChartRetraction (R := R) (k := k) w f) :=
  fractionValuation_algebraMap _ _ _

end ClosedRetractionField
end CartierSections

end

end OAI

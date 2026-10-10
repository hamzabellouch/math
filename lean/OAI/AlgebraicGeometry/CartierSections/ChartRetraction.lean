import OAI.AlgebraicGeometry.CartierSections.ExpansionValuation
import OAI.AlgebraicGeometry.CartierSections.ClosedCharts

namespace OAI

/-!
# Monomial retractions on closed étale charts

The completed local coordinate isomorphism defines a faithful formal
expansion. Its monomial valuation allows boundary faces with zero weights.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections
/-- Equal ideals have canonically isomorphic completions. -/
noncomputable def completionIdealCongr {P A : Type*} [CommRing P] [CommRing A]
    [Algebra P A] (I J : Ideal A) (h : I = J) :
    AdicCompletion I A ≃ₐ[P] AdicCompletion J A := by
  subst J
  exact AlgEquiv.refl

section ClosedRetraction
attribute [local instance] polynomialOrigin_isMaximal
universe u
variable {σ k R A : Type u} [Fintype σ] [Field k] [IsAlgClosed k]
  [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) A]
  [Algebra k A] [IsScalarTower k (MvPolynomial σ k) A]
  [Algebra R A] [IsScalarTower (MvPolynomial σ k) R A]
  [IsLocalization.AtPrime R (MvPolynomial.idealOfVars σ k)]
  [IsLocalHom (algebraMap R A)] [Algebra.FormallyUnramified R A]
  [Algebra.EssFiniteType R A] [Algebra.FormallyEtale (MvPolynomial σ k) A]

include R

/-- The completed coordinate isomorphism at a closed étale point. -/
noncomputable def closedChartEquiv : MvPowerSeries σ k ≃ₐ[MvPolynomial σ k]
    AdicCompletion (IsLocalRing.maximalIdeal A) A := by
  exact (polynomialChartSeriesEquiv
    (closed_chart_base_bijective (R := R) (A := A) (σ := σ) (k := k))).trans
    (completionIdealCongr _ _
      (closed_chart_maximalIdeal (R := R) (A := A) (σ := σ) (k := k)))

noncomputable def closedChartExpansion : A →ₐ[k] MvPowerSeries σ k :=
  chartSeriesExpansion (closedChartEquiv (σ := σ) (k := k) (A := A) (R := R))

omit [IsNoetherianRing A] in
@[simp] lemma closedChartExpansion_coordinate (i : σ) :
    closedChartExpansion (σ := σ) (k := k) (A := A) (R := R)
      (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) = MvPowerSeries.X i :=
  chartSeriesExpansion_coordinate _ i

/-- The monomial valuation pulled back by the formal coordinate expansion. -/
noncomputable def closedChartRetraction (w : σ → ℝ≥0) : AddValuation A ENNReal :=
  expansionValuation (closedChartExpansion (σ := σ) (k := k) (A := A) (R := R)) w

lemma closedChartExpansion_injective :
    Function.Injective (closedChartExpansion (σ := σ) (k := k) (A := A) (R := R)) := by
  let e := closedChartEquiv (σ := σ) (k := k) (A := A) (R := R)
  let : Algebra A (MvPowerSeries σ k) := (completionExpansion e.toRingEquiv).toAlgebra
  let : Module.FaithfullyFlat A (MvPowerSeries σ k) :=
    completionExpansion_faithfullyFlat e.toRingEquiv
  exact FaithfulSMul.algebraMap_injective A (MvPowerSeries σ k)

lemma closedChartRetraction_finite (w : σ → ℝ≥0) {f : A} (hf : f ≠ 0) :
    closedChartRetraction (σ := σ) (k := k) (A := A) (R := R) w f < ⊤ :=
  expansionValuation_finite _ (closedChartExpansion_injective (σ := σ) (k := k) (A := A) (R := R)) w hf

end ClosedRetraction
end CartierSections

end

end OAI

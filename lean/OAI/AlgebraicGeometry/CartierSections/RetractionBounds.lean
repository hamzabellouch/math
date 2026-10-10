import OAI.AlgebraicGeometry.CartierSections.FieldRetraction
import OAI.AlgebraicGeometry.CartierSections.ValuationBounds

namespace OAI

/-!
# Valuation inequalities for monomial retractions

In a closed étale chart, monomial retraction decreases the values of regular
functions. The inequality passes to the valuation of the fraction field.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections
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

/-- Retraction decreases all regular-function values in a Noetherian
closed étale chart, including boundary faces with zero weights. -/
lemma closedChartRetraction_le [CharZero k]
    (v : AddValuation A ENNReal) (B : Finset σ) (w : σ → ℝ≥0)
    (hwzero : ∀ i ∉ B, w i = 0)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) =
      (w i : ENNReal)) (f : A) : closedChartRetraction (σ := σ) (k := k) (A := A) (R := R) w f ≤ v f := by
  classical
  let e := closedChartEquiv (σ := σ) (k := k) (A := A) (R := R)
  let θ := closedChartExpansion (σ := σ) (k := k) (A := A) (R := R)
  let : Algebra A (MvPowerSeries σ k) := (completionExpansion e.toRingEquiv).toAlgebra
  let : Module.FaithfullyFlat A (MvPowerSeries σ k) :=
    completionExpansion_faithfullyFlat e.toRingEquiv
  let : IsScalarTower k A (MvPowerSeries σ k) := IsScalarTower.of_algebraMap_eq'
    (show algebraMap k (MvPowerSeries σ k) =
      (algebraMap A (MvPowerSeries σ k)).comp (algebraMap k A) from θ.comp_algebraMap.symm)
  by_cases hf : f = 0
  · subst f; simp
  obtain ⟨d, hd, he⟩ := FormalMonomial.value_attained w
    (show θ f ≠ 0 from fun h => hf (by
      apply closedChartExpansion_injective (σ := σ) (k := k) (A := A) (R := R)
      simpa [θ] using h))
  have hweight (a : σ →₀ ℕ) (ha : MvPowerSeries.coeff a (θ f) ≠ 0) :
      realWeight (fun i => (w i : ℝ)) d ≤ realWeight (fun i => (w i : ℝ)) a := by
    rw [← coe_finsupp_weight, ← coe_finsupp_weight]
    exact NNReal.coe_le_coe.mpr (ENNReal.coe_le_coe.mp
      (he ▸ FormalMonomial.value_le_weight w ha))
  have h := valuation_ge_initial_weight θ (closedChartExpansion_coordinate (σ := σ) (k := k) (A := A) (R := R))
    (show θ.toRingHom = algebraMap A (MvPowerSeries σ k) from rfl)
    v B (fun i => (w i : ℝ)) (fun i => (w i).property)
    (fun i hi => by simp [hwzero i hi])
    (fun i hi => by simpa only [ENNReal.ofReal_coe_nnreal] using hz i hi)
    f _ hweight
  change FormalMonomial.value w (θ f) ≤ v f
  rw [he]
  simpa only [← coe_finsupp_weight, ENNReal.ofReal_coe_nnreal] using h

end ClosedRetraction

section ClosedRetractionField
universe u
attribute [local instance] polynomialOrigin_isMaximal
variable {σ k R A K : Type u} [Fintype σ] [Field k] [IsAlgClosed k]
  [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) A]
  [Algebra k A] [IsScalarTower k (MvPolynomial σ k) A]
  [Algebra R A] [IsScalarTower (MvPolynomial σ k) R A]
  [IsLocalization.AtPrime R (MvPolynomial.idealOfVars σ k)]
  [IsLocalHom (algebraMap R A)] [Algebra.FormallyUnramified R A]
  [Algebra.EssFiniteType R A] [Algebra.FormallyEtale (MvPolynomial σ k) A]

lemma closedChartFieldRetraction_le [CharZero k]
    (v : AddValuation A ENNReal) (B : Finset σ) (w : σ → NNReal)
    (hwzero : ∀ i ∉ B, w i = 0)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) =
      (w i : ENNReal)) (f : A) :
    closedChartFieldRetraction (σ := σ) (k := k) (R := R) (A := A) (K := K) w (algebraMap A K f) ≤
      nonnegToExtendedReal (v f) := by
  rw [closedChartFieldRetraction_regular]
  exact nonnegToExtendedReal_monotone
    (closedChartRetraction_le (σ := σ) (k := k) (A := A) (R := R) v B w hwzero hz f)

end ClosedRetractionField
end CartierSections

end

end OAI

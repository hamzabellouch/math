import OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily
import OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity
import OAI.NumberTheory.PiExponent.Approximation.OrdinarySliceComparison
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity
import OAI.NumberTheory.PiExponent.Jets.TransverseSliceComparison

namespace OAI

noncomputable section
namespace PiExponent.PersistentWeightComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity NormalBasisProducts

def comparisonConstant (m : ℕ) (sigma : ℝ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) * (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)

def UniformRectangles (n : ℕ) (cost : Fin n → ℝ) (epsilon N : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ n → ∀ B : Fin k → Fin n, ∀ i,
    2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i

theorem eventually_uniformRectangles (n : ℕ) (cost : Fin n → ℝ)
    (hcost : ∀ i, 0 < cost i) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, UniformRectangles n cost epsilon N :=
  eventually_uniform_cutoff n cost hcost epsilon hepsilon

theorem logarithmic_normal_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (hQ : Q ∈ (frameDerivativeIdeal cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ frameDerivativeIdeal cost bound F,
      ∀ word : List (Fin (m + 1)),
        frameWordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          polynomialFrameWord m word p ∈ Q) :
    CurveComponentRigidity.NormalProductComparison Q hY
      (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, comparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ m + 1 := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (FrameEquationFamily.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := FrameEquationFamily.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := TransverseSliceComparison.comparison_of_normal_basis Q
    (CurveComponentRigidity.residueY_ne_zero Q hY) A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (FrameEquationFamily.equations cost bound F)
    (by simpa only [FrameEquationFamily.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [FrameEquationFamily.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (by omega) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, comparisonConstant] using hc)

theorem logarithmic_persistent_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (FramePolynomial m)) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) :
    CurveComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (comparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F P hY := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact logarithmic_normal_comparison rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q (fun h => hY (hQP h)) hQr hvanish

theorem ordinary_normal_comparison {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime]
    (hQ : Q ∈ (OrdinaryDerivatives.ideal n cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ OrdinaryDerivatives.ideal n cost bound F,
      ∀ word : List (Fin n),
        DerivativeIdeals.wordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          OrdinaryDerivatives.word n word p ∈ Q) :
    OrdinaryComponentRigidity.NormalProductComparison Q
      (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, comparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (OrdinaryDerivatives.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := OrdinaryDerivatives.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := OrdinarySliceComparison.comparison_of_normal_basis Q A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (OrdinaryDerivatives.equations cost bound F)
    (by simpa only [OrdinaryDerivatives.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [OrdinaryDerivatives.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (hka.trans hn) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, comparisonConstant] using hc)

theorem ordinary_persistent_comparison {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (d : ℕ) (P : Ideal (OrdinaryDerivatives.Polynomial n)) :
    OrdinaryComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (comparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F d P := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact ordinary_normal_comparison hn rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q hQr hvanish

end PiExponent.PersistentWeightComparison
end

end OAI

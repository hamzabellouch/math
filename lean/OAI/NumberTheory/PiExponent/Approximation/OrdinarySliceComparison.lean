import OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts
import OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout

namespace OAI

noncomputable section
namespace PiExponent.OrdinarySliceComparison

open scoped BigOperators
open NormalBasisRigidity NormalBasisProducts TransverseWeightedMultiplicity
open OrdinaryDerivatives DerivativeIdeals

theorem comparison_of_normal_basis {n : ℕ}
    (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime]
    (A : Finset (Fin n)) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin n)
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ (B j))))
    {J : Type*} (f : J → OrdinaryDerivatives.Polynomial n)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ l : List (Fin n),
      wordCost cost l ≤ epsilon * N → OrdinaryDerivatives.word n l p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := PrimeWeightedBezout.weighted_prime_length_bound
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := OrdinaryMultiplicity.prime_rectangular_length_lower n A.card Q B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using h

end PiExponent.OrdinarySliceComparison
end

end OAI

import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts
import OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound

namespace OAI

noncomputable section
namespace PiExponent.TransverseSliceComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity
open TransverseWeightedMultiplicity WeightedSliceDegree

def residueCoordinates {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (i : Fin (m + 1)) : Q.ResidueField := primeResidueMap Q (MvPolynomial.X i)

def sliceEquations {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (A : Finset (Fin (m + 1))) {J : Type*} (f : J → FramePolynomial m) :
    J → MvPolynomial (Fin A.card) Q.ResidueField :=
  fun j => enumeratedSliceMap A (residueCoordinates Q) (f j)

def slicePoint {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (A : Finset (Fin (m + 1))) : Fin A.card → Q.ResidueField :=
  fun i => residueCoordinates Q (A.equivFin.symm i)

theorem comparison_of_actual_slice {m : ℕ}
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (A : Finset (Fin (m + 1))) (hk : 0 < A.card)
    (B : Fin A.card → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    {J : Type*} (f : J → FramePolynomial m)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ epsilon * N → polynomialFrameWord m word p ∈ Q)
    (hminimal : WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (Ideal.span (Set.range (sliceEquations Q A f))).minimalPrimes)
    (hlength : Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ (Ideal.span (Set.range f)).map
          (algebraMap (FramePolynomial m) (Localization.AtPrime Q))) =
      WeightedBezout.pointLength (slicePoint Q A)
        (Ideal.span (Set.range (sliceEquations Q A f)))) :
    (∏ i : Fin A.card, (rho (A.equivFin.symm i) : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hsliceDegree : ∀ j, ∀ d ∈ (sliceEquations Q A f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho (A.equivFin.symm i) : ℝ)) ≤ N := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (rho i : ℝ)) (fun i => (hrhoR i).le) N (f j) (hdegree j)
  obtain ⟨L, hL, hupper⟩ := WeightedBezout.rational_pointLength_bound
    Q.ResidueField (sliceEquations Q A f) (slicePoint Q A)
    (fun i => rho (A.equivFin.symm i)) (fun i => hrho _) N hN.le hsliceDegree hminimal
  have hlower := prime_frame_rectangular_length_lower m A.card Q hy B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  rw [hlength, hL] at hlower
  apply weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN _ hupper
  exact_mod_cast hlower

theorem comparison_of_normal_basis {m : ℕ}
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (A : Finset (Fin (m + 1))) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    {J : Type*} (f : J → FramePolynomial m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ epsilon * N → polynomialFrameWord m word p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := PrimeWeightedBezout.weighted_prime_length_bound
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := prime_frame_rectangular_length_lower m A.card Q hy B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using h

end PiExponent.TransverseSliceComparison
end

end OAI

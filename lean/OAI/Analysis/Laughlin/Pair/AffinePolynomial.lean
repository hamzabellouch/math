import OAI.Analysis.Laughlin.Pair.DiagonalCube
import OAI.Analysis.Laughlin.Pair.MomentKernel

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators Polynomial.Bivariate

noncomputable def pairAffinePolynomial (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : PairDiagonal.Poly :=
  ∑ x, ∑ y, monomial y.val (monomial x.val (weightedPairCoordinate Q ψ x y))

theorem pairAffinePolynomial_antisymmetric (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y) :
    Bivariate.swap (pairAffinePolynomial Q ψ) = -pairAffinePolynomial Q ψ := by
  unfold pairAffinePolynomial
  simp only [map_sum, Bivariate.swap_monomial_monomial]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [weightedPairCoordinate_swap Q ψ ha x y]
  simp

theorem diagonal_jet_monomial_coeff (i j n : ℕ) (a : ℂ) :
    ((monomial j (monomial i a)).derivative.eval (X : Polynomial ℂ)).coeff n =
      if i+j = n+1 then (j : ℂ)*a else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_monomial, eval_monomial]
    have hm : (monomial i a : Polynomial ℂ)*(j.succ : Polynomial ℂ) =
        monomial i (a*(j.succ : ℂ)) := by
      have hc : (j.succ : Polynomial ℂ) = C (j.succ : ℂ) := by simp
      rw [hc, monomial_mul_C]
    rw [Nat.succ_sub_one, hm, monomial_mul_X_pow, coeff_monomial]
    have he : i+j = n ↔ i+j.succ = n+1 := by omega
    simp only [he, mul_comm]

theorem pairAffinePolynomial_jet_coeff (Q n : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    ((pairAffinePolynomial Q ψ).derivative.eval (X : Polynomial ℂ)).coeff n =
      ∑ x, ∑ y, if x.val+y.val = n+1 then
        (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0 := by
  unfold pairAffinePolynomial
  simp only [derivative_sum, eval_finsetSum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact diagonal_jet_monomial_coeff x.val y.val n _

theorem pair_kernel_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y)
    (hk : ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) :
    PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ := by
  apply PairDiagonal.cube_dvd_of_antisymmetric_first_jet
  · exact pairAffinePolynomial_antisymmetric Q ψ ha
  · ext n
    rw [pairAffinePolynomial_jet_coeff, coeff_zero]
    exact pair_jet_coefficient_zero Q n ψ ha (pairMoment_zero_of_pair_kernel Q hQ ψ hk n)

end Laughlin

end OAI

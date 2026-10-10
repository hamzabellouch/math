import OAI.Analysis.Laughlin.Pair.Homogenize

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem homogeneousEval_cube {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (p : Polynomial R) (hp : p.natDegree ≤ 1) :
    homogeneousEval f u v 3 (p^3) = (homogeneousEval f u v 1 p)^3 := by
  have h := homogenize_finsetProd (s := Finset.range 3) (p := fun _ => p)
    (n := fun _ => 1) (fun _ _ => hp)
  have he : (p^3).homogenize 3 = (p.homogenize 1)^3 := by simpa using h
  simp [homogeneousEval, he]

theorem homogeneousEval_linear {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (a b : R) :
    homogeneousEval f u v 1 (C a - X * C b) = f a * u - v * f b := by
  simp [homogeneousEval, homogenize_sub, show X * C b = C b * X by ring,
    MvPolynomial.eval₂_mul]
  ring

theorem linear_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (hb : b ≠ 0) : (C a - X * C b).natDegree = 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_mul_le).trans (by simp)))
  · simpa using neg_ne_zero.mpr hb

noncomputable def pairPartialPolynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : Polynomial R :=
  homogeneousEval (Polynomial.mapRingHom f) (C uj) (C vj) Q
    (pairAffinePolynomial Q ψ)

theorem pairPartialPolynomial_expansion {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairPartialPolynomial f uj vj Q ψ = ∑ x, ∑ y,
      monomial x.val (f (weightedPairCoordinate Q ψ x y) * vj^y.val * uj^(Q-y.val)) := by
  unfold pairPartialPolynomial pairAffinePolynomial
  simp only [homogeneousEval_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [homogeneousEval_monomial _ _ _ _ _ (Nat.le_of_lt_succ y.isLt)]
  change (monomial x.val (weightedPairCoordinate Q ψ x y)).map f *
    C vj ^ y.val * C uj ^ (Q-y.val) = _
  simp only [map_monomial, ← map_pow, monomial_mul_C]

theorem pairPartialPolynomial_degree {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    (pairPartialPolynomial f uj vj Q ψ).natDegree ≤ Q := by
  rw [pairPartialPolynomial_expansion]
  apply natDegree_sum_le_of_forall_le
  intro x hx
  apply natDegree_sum_le_of_forall_le
  intro y hy
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ x.isLt)

theorem pairAffinePolynomial_degree (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    (pairAffinePolynomial Q ψ).natDegree ≤ Q := by
  apply natDegree_sum_le_of_forall_le
  intro x hx
  apply natDegree_sum_le_of_forall_le
  intro y hy
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ y.isLt)

theorem pairPartialPolynomial_cube {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    (C vj - X * C uj)^3 ∣ pairPartialPolynomial f uj vj Q ψ := by
  have hd := homogeneousEval_dvd (Polynomial.mapRingHom f) (C uj) (C vj)
    hc (pairAffinePolynomial_degree Q ψ)
  have hdeg : (PairDiagonal.diagonal^3).natDegree = 3 := by
    simp [PairDiagonal.diagonal, natDegree_pow]
  rw [hdeg, homogeneousEval_cube _ _ _ _ (by simp [PairDiagonal.diagonal])] at hd
  have he : homogeneousEval (Polynomial.mapRingHom f) (C uj) (C vj) 1
      PairDiagonal.diagonal = C vj - X * C uj := by
    simp [homogeneousEval, PairDiagonal.diagonal]
  simpa only [he, pairPartialPolynomial] using hd

end Laughlin

end OAI

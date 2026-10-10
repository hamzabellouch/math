import OAI.Analysis.Laughlin.Pair.HomogeneousCube
import OAI.Analysis.Laughlin.Polynomial.Polynomial

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

noncomputable def pairSpinorPolynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (ui vi uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : R :=
  ∑ x, ∑ y, f (weightedPairCoordinate Q ψ x y) *
    (ui^(Q-x.val) * vi^x.val) * (uj^(Q-y.val) * vj^y.val)

theorem pairSpinorPolynomial_homogeneousEval {R : Type*} [CommRing R]
    (f : ℂ →+* R) (ui vi uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairSpinorPolynomial f ui vi uj vj Q ψ =
      homogeneousEval (RingHom.id R) ui vi Q (pairPartialPolynomial f uj vj Q ψ) := by
  rw [pairPartialPolynomial_expansion]
  simp only [homogeneousEval_sum, pairSpinorPolynomial]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [homogeneousEval_monomial _ _ _ _ _ (Nat.le_of_lt_succ x.isLt)]
  simp only [RingHom.id_apply]
  ring

theorem pairSpinorPolynomial_cube {R : Type*} [CommRing R] [IsDomain R]
    (f : ℂ →+* R) (ui vi uj vj : R) (huj : uj ≠ 0) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    (ui*vj-uj*vi)^3 ∣ pairSpinorPolynomial f ui vi uj vj Q ψ := by
  have hd := homogeneousEval_dvd (RingHom.id R) ui vi
    (pairPartialPolynomial_cube f uj vj Q ψ hc)
    (pairPartialPolynomial_degree f uj vj Q ψ)
  have hdeg : ((C vj-X*C uj)^3).natDegree = 3 := by
    rw [natDegree_pow, linear_natDegree vj uj huj]
  rw [hdeg, homogeneousEval_cube _ _ _ _ (by rw [linear_natDegree vj uj huj]),
    homogeneousEval_linear] at hd
  rw [pairSpinorPolynomial_homogeneousEval]
  simpa only [RingHom.id_apply, mul_comm vj ui, mul_comm vi uj] using hd

theorem pairSpinorPolynomial_bracket_cube {N Q : ℕ} (i j : Fin N)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    bracket i j^3 ∣ pairSpinorPolynomial MvPolynomial.C
      (MvPolynomial.X (i,false)) (MvPolynomial.X (i,true))
      (MvPolynomial.X (j,false)) (MvPolynomial.X (j,true)) Q ψ := by
  exact pairSpinorPolynomial_cube _ _ _ _ _ (MvPolynomial.X_ne_zero _) Q ψ hc

end Laughlin

end OAI

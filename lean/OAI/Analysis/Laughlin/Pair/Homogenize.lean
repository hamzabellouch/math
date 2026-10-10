import Mathlib.Algebra.Polynomial.Homogenize
import OAI.Analysis.Laughlin.Pair.AffinePolynomial

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem homogenize_dvd_of_degree_le {R : Type*} [CommRing R] [IsDomain R]
    {p q : Polynomial R} {n : ℕ} (hd : p ∣ q) (hn : q.natDegree ≤ n) :
    p.homogenize p.natDegree ∣ q.homogenize n := by
  have he : q.homogenize n = q.homogenize q.natDegree *
      (1 : Polynomial R).homogenize (n-q.natDegree) := by
    rw [← homogenize_mul q 1 le_rfl (by simp), mul_one,
      Nat.add_sub_of_le hn]
  rw [he]
  exact (homogenize_dvd hd).trans (dvd_mul_right _ _)

noncomputable def homogeneousEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (n : ℕ) (p : Polynomial R) : S :=
  MvPolynomial.eval₂ f (fun k : Fin 2 => if k = 0 then v else u) (p.homogenize n)

theorem homogeneousEval_monomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (n k : ℕ) (h : k ≤ n) (a : R) :
    homogeneousEval f u v n (monomial k a) = f a * v^k * u^(n-k) := by
  simp [homogeneousEval, homogenize_monomial h, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

theorem homogeneousEval_sum {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (n : ℕ) (s : Finset ι) (p : ι → Polynomial R) :
    homogeneousEval f u v n (∑ k ∈ s, p k) =
      ∑ k ∈ s, homogeneousEval f u v n (p k) := by
  simp [homogeneousEval]

theorem homogeneousEval_dvd {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (u v : S) {p q : Polynomial R} {n : ℕ}
    (hd : p ∣ q) (hn : q.natDegree ≤ n) :
    homogeneousEval f u v p.natDegree p ∣ homogeneousEval f u v n q :=
  MvPolynomial.eval₂_dvd _ _ (homogenize_dvd_of_degree_le hd hn)

end Laughlin

end OAI

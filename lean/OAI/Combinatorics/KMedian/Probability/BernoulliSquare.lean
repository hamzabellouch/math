import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliPolynomial
import OAI.Combinatorics.KMedian.Binary.BooleanMonomials

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n m : ℕ}

def pairSet (S : Fin m → Finset (Fin n)) (a : Fin (m*m)) : Finset (Fin n) :=
  S (finProdFinEquiv.symm a).1 ∪ S (finProdFinEquiv.symm a).2

def pairCoefficient (c : Fin m → ℚ) (a : Fin (m*m)) : ℚ :=
  c (finProdFinEquiv.symm a).1*c (finProdFinEquiv.symm a).2

theorem polynomial_square (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ)
    (q : Fin n → Bool) : (polynomial S c q)^2=polynomial (pairSet S) (pairCoefficient c) q := by
  unfold polynomial pairSet pairCoefficient
  rw [← (finProdFinEquiv : Fin m × Fin m ≃ Fin (m*m)).sum_comp]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,pow_two,sum_mul,mul_sum]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [← product_union]
  ring

theorem pairSet_card (S : Fin m → Finset (Fin n)) (hS : ∀ j, (S j).card ≤ 2)
    (a : Fin (m*m)) : (pairSet S a).card ≤ 4 := by
  apply (card_union_le _ _).trans
  have h := hS (finProdFinEquiv.symm a).1
  have h' := hS (finProdFinEquiv.symm a).2
  omega

theorem quadratic_second_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ 2) :
    (run (d := 4) p hp n).moment (fun q => (polynomial S c q)^2)=
      ∑ a : Fin (m*m), pairCoefficient c a*∏ i∈pairSet S a,p i := by
  simp_rw [polynomial_square]
  exact polynomial_moment p hp (pairSet S) (pairCoefficient c) (pairSet_card S hS)

end MetricKMedian.SparseBernoulli

end OAI

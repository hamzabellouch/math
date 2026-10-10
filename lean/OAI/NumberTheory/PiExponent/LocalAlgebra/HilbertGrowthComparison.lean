import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree

namespace OAI

namespace PiExponentJets.W24

open Polynomial

theorem natDegree_le_of_eventual_polynomial_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (N : ℕ)
    (hle : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hn
  have hdeg : q.degree < p.degree := degree_lt_degree (Nat.lt_of_not_ge hn)
  have hnonneg := W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (q - p) N (fun n hn => by simpa only [eval_sub] using sub_nonneg.mpr (hle n hn))
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hnonneg
  exact (not_le_of_gt hp) (neg_nonneg.mp hnonneg)

theorem natDegree_affine_comp_le (p : Polynomial ℚ) (a b : ℚ) :
    (p.comp (C a * X + C b)).natDegree ≤ p.natDegree := by
  have ha : (C a * X + C b : Polynomial ℚ).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [natDegree_X] using natDegree_C_mul_le a (X : Polynomial ℚ)
  exact (natDegree_comp_le).trans ((Nat.mul_le_mul_left _ ha).trans_eq (Nat.mul_one _))

theorem natDegree_eq_of_polynomial_growth_bounds
    (q lower upper : Polynomial ℚ) (d : ℕ)
    (hql : 0 < q.leadingCoeff) (hll : 0 < lower.leadingCoeff)
    (hld : lower.natDegree = d) (hud : upper.natDegree ≤ d)
    (a b c e : ℚ) (N : ℕ)
    (hlo : ∀ n : ℕ, N ≤ n → lower.eval (n : ℚ) ≤ q.eval (a * n + b))
    (hup : ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) ≤ upper.eval (c * n + e)) :
    q.natDegree = d := by
  have hlow : lower.natDegree ≤ (q.comp (C a * X + C b)).natDegree :=
    natDegree_le_of_eventual_polynomial_le lower _ hll N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hlo)
  have hupp : q.natDegree ≤ (upper.comp (C c * X + C e)).natDegree :=
    natDegree_le_of_eventual_polynomial_le q _ hql N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hup)
  exact le_antisymm
    (hupp.trans ((natDegree_affine_comp_le upper c e).trans hud))
    (hld ▸ hlow.trans (natDegree_affine_comp_le q a b))

end PiExponentJets.W24

end OAI

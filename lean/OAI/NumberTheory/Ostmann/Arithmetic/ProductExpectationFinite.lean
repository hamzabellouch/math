import OAI.NumberTheory.Ostmann.Arithmetic.ProductExpectation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.ProductExpectation
open scoped BigOperators

theorem eq_product_sum {K : Type*} : ∀ {n : ℕ} (S : Fin n → Finset K)
    (μ : Fin n → K → ℝ) (f : (Fin n → K) → ℝ),
    expectation S μ f = ∑ x ∈ Fintype.piFinset S, (∏ i, μ i (x i))*f x
  | 0, S, μ, f => by
    classical
    simp only [expectation, Fintype.piFinset_of_isEmpty,
      Fintype.prod_empty, one_mul, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg f (Subsingleton.elim _ _)
  | n+1, S, μ, f => by
    classical
    have hS := Finset.filter_piFinset_eq_map_consEquiv S (fun _ => True)
    simp only [Finset.filter_true] at hS
    rw [expectation, eq_product_sum, hS, Finset.sum_map, Finset.sum_product]
    simp only [Equiv.toEmbedding_apply, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    change (∏ i : Fin n, μ i.succ (x i)) * (μ 0 a * f (Fin.cons a x)) =
      (μ 0 a * ∏ i : Fin n, μ i.succ (x i))*f (Fin.cons a x)
    ring

end Ostmann.Arithmetic.ProductExpectation

end

end OAI

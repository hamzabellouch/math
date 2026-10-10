import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.ProductExpectation
open scoped BigOperators

def expectation {K : Type*} : {n : ℕ} → (Fin n → Finset K) →
    (Fin n → K → ℝ) → ((Fin n → K) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | _n+1, S, μ, f => expectation (Fin.tail S) (Fin.tail μ)
      (fun x => ∑ a ∈ S 0, μ 0 a * f (Fin.cons a x))

theorem mono {K : Type*} : ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
    (_hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a) {f g : (Fin n → K) → ℝ}
    (_hfg : ∀ x, f x ≤ g x), expectation S μ f ≤ expectation S μ g
  | 0, _, _, _, _, _, hfg => hfg _
  | n+1, S, μ, hμ, f, g, hfg => by
    apply mono (Fin.tail S) (Fin.tail μ) (fun i => hμ i.succ)
    intro x
    exact Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_left (hfg (Fin.cons a x)) (hμ 0 a ha)

theorem const {K : Type*} : ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
    (_hμ : ∀ i, ∑ a ∈ S i, μ i a = 1) (c : ℝ),
    expectation S μ (fun _ => c) = c
  | 0, _, _, _, _ => rfl
  | n+1, S, μ, hμ, c => by
    simp only [expectation, ← Finset.sum_mul, hμ, one_mul]
    exact const (Fin.tail S) (Fin.tail μ) (fun i => hμ i.succ) c

theorem add {K : Type*} : ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
    (f g : (Fin n → K) → ℝ),
    expectation S μ (fun x => f x + g x) = expectation S μ f + expectation S μ g
  | 0, _, _, _, _ => rfl
  | n+1, S, μ, f, g => by
    simp only [expectation, mul_add, Finset.sum_add_distrib]
    exact add (Fin.tail S) (Fin.tail μ) _ _

end Ostmann.Arithmetic.ProductExpectation

end

end OAI

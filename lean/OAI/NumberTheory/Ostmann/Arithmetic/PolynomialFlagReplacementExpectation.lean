import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialRootProbability

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacement
open scoped BigOperators
open ProductExpectation

theorem expectation_mono_support {K : Type*} :
    ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
      (_hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a) {f g : (Fin n → K) → ℝ}
      (_hfg : ∀ x, (∀ i, x i ∈ S i) → f x ≤ g x), expectation S μ f ≤ expectation S μ g
  | 0,_,_,_,_,_,hfg => hfg _ (fun i => Fin.elim0 i)
  | n+1,S,μ,hμ,f,g,hfg => by
    apply expectation_mono_support (Fin.tail S) (Fin.tail μ) (fun i => hμ i.succ)
    intro x hx
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (hμ 0 a ha)
    apply hfg
    intro i
    exact Fin.cases ha (fun j => hx j) i

lemma expectation_zero {K : Type*} : ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ),
    expectation S μ (fun _ => 0)=0
  | 0,_,_ => rfl
  | n+1,S,μ => by
    simp only [expectation,mul_zero,Finset.sum_const_zero]
    exact expectation_zero _ _

lemma expectation_nonneg {K : Type*} {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
    (hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a) (f : (Fin n → K) → ℝ)
    (hf : ∀ x, (∀ i, x i ∈ S i) → 0 ≤ f x) : 0 ≤ expectation S μ f := by
  simpa only [expectation_zero] using expectation_mono_support S μ hμ hf

lemma expectation_const_mul {K : Type*} :
    ∀ {n : ℕ} (S : Fin n → Finset K) (μ : Fin n → K → ℝ)
      (c : ℝ) (f : (Fin n → K) → ℝ),
      expectation S μ (fun x => c*f x)=c*expectation S μ f
  | 0,_,_,_,_ => rfl
  | n+1,S,μ,c,f => by
    simp only [expectation,show ∀ a y : ℝ, a*(c*y)=c*(a*y) from fun _ _ => by ring,← Finset.mul_sum]
    exact expectation_const_mul _ _ _ _

lemma expectation_finset_sum {K J : Type*} [DecidableEq J] {n : ℕ}
    (S : Fin n → Finset K) (μ : Fin n → K → ℝ) (F : Finset J)
    (f : J → (Fin n → K) → ℝ) :
    expectation S μ (fun x => ∑ j ∈ F, f j x) = ∑ j ∈ F, expectation S μ (f j) := by
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,expectation_zero]
  | @insert j F hj ih =>
    simp only [Finset.sum_insert hj,ProductExpectation.add,ih]

end Ostmann.Arithmetic.PolynomialFlagReplacement

end

end OAI

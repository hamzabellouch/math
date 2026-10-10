import OAI.NumberTheory.Ostmann.Arithmetic.AccidentalDivisibility
import OAI.NumberTheory.Ostmann.Arithmetic.ProductExpectation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialRootProbability
open scoped BigOperators
open MvPolynomial ProductExpectation

theorem weighted_zero_bound {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) K) (_hP : P ≠ 0)
      (S : Fin n → Finset K) (μ : Fin n → K → ℝ) (α : ℝ) (_hα : 0 ≤ α)
      (_hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a)
      (_hmass : ∀ i, ∑ a ∈ S i, μ i a = 1)
      (_hatom : ∀ i a, a ∈ S i → μ i a ≤ α),
      expectation S μ (fun x => if eval x P = 0 then 1 else 0) ≤
        (P.totalDegree : ℝ) * α
  | 0, P, hP, S, μ, α, hα, hμ, hmass, hatom => by
    rw [P.eq_C_of_isEmpty] at hP ⊢
    simp only [expectation, eval_C, totalDegree_C, Nat.cast_zero, zero_mul]
    simp [C_ne_zero.mp hP]
  | n+1, P, hP, S, μ, α, hα, hμ, hmass, hatom => by
    let P' := finSuccEquiv K n P
    let k := P'.natDegree
    let Q := P'.leadingCoeff
    have hP' : P' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hP
    have hQ : Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP'
    have hdegree : Q.totalDegree+k ≤ P.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le P k hQ
    have hfiber : ∀ x : Fin n → K,
        (∑ a ∈ S 0, μ 0 a * (if eval (Fin.cons a x) P=0 then 1 else 0)) ≤
          (if eval x Q=0 then 1 else 0) + (k:ℝ)*α := by
      intro x
      by_cases hx : eval x Q = 0
      · rw [ite_eq_left hx]
        calc
          _ ≤ ∑ a ∈ S 0, μ 0 a := Finset.sum_le_sum fun a ha => by
            split_ifs <;> simp [hμ 0 a ha]
          _ = 1 := hmass 0
          _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hα)
      · rw [ite_eq_right hx, zero_add]
        let Px := P'.map (eval x)
        have hPx : Px ≠ 0 := by
          intro h
          apply hx
          have hh := congrArg (fun f : Polynomial K => f.coeff k) h
          simpa only [Px, Polynomial.coeff_map, Polynomial.coeff_zero,
            k, Q, Polynomial.leadingCoeff] using hh
        have hPxdeg : Px.natDegree ≤ k := Polynomial.natDegree_map_le
        calc
          _ = ∑ a ∈ S 0 with Px.eval a=0, μ 0 a := by
            simp only [eval_eq_eval_mv_eval', Finset.sum_filter, Px, P']
            apply Finset.sum_congr rfl
            intro a ha
            split_ifs <;> simp
          _ ≤ (Px.natDegree:ℝ)*α :=
            AccidentalDivisibility.weighted_polynomial_roots Px hPx (S 0) (μ 0) hα (hatom 0)
          _ ≤ (k:ℝ)*α := mul_le_mul_of_nonneg_right (by exact_mod_cast hPxdeg) hα
    calc
      _ ≤ expectation (Fin.tail S) (Fin.tail μ)
          (fun x => (if eval x Q=0 then 1 else 0)+(k:ℝ)*α) :=
        ProductExpectation.mono (Fin.tail S) (Fin.tail μ) (fun i => hμ i.succ) hfiber
      _ = expectation (Fin.tail S) (Fin.tail μ)
          (fun x => if eval x Q=0 then 1 else 0)+(k:ℝ)*α := by
        rw [ProductExpectation.add]
        exact congrArg (fun t => expectation (Fin.tail S) (Fin.tail μ)
          (fun x => if eval x Q=0 then 1 else 0) + t)
          (ProductExpectation.const (Fin.tail S) (Fin.tail μ)
            (fun i => hmass i.succ) ((k:ℝ)*α))
      _ ≤ (Q.totalDegree:ℝ)*α+(k:ℝ)*α := add_le_add
        (weighted_zero_bound Q hQ (Fin.tail S) (Fin.tail μ) α hα
          (fun i => hμ i.succ) (fun i => hmass i.succ) (fun i => hatom i.succ)) le_rfl
      _ ≤ (P.totalDegree:ℝ)*α := by
        rw [← add_mul, ← Nat.cast_add]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hα

end Ostmann.Arithmetic.PolynomialRootProbability

end

end OAI

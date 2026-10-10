import OAI.NumberTheory.Ostmann.Construction.FinalReassignments
import OAI.NumberTheory.Ostmann.Arithmetic.SymmetrizedPairBound

namespace OAI

/-! # The final comparison for the constructed parity-preserving family -/

namespace Ostmann

open scoped BigOperators Classical

theorem final_permutation_comparison {X : Type*} [Fintype X] (n m : ℕ)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (T B E : ℝ) (hT : ∑ x, μ x ≤ T) (hE : 0 ≤ E)
    (A : FinalParityReassignments n m → X → ℂ) (η : ℂ)
    (hmean : ∀ e, ∑ x, (μ x : ℂ) * A e x = η)
    (hpair : ∀ e f, ‖∑ x, (μ x : ℂ) * (A e x * star (A f x))‖ ≤ if e = f then B else E) :
    ‖η‖ ^ 2 ≤ T * (B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + E) := by
  classical
  let J := FinalParityReassignments n m
  have hcard : (Fintype.card J : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := J)
  have hmeanAvg : ∑ x, (μ x : ℂ) * finiteFamilyAverage A x = η := by
    calc
      _ = (Fintype.card J : ℂ)⁻¹ * ∑ e : J, ∑ x, (μ x : ℂ) * A e x := by
        simp only [finiteFamilyAverage, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = η := by
        simp only [hmean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have henergy := finiteFamilyAverage_good_bad_bound μ A (fun e : J => e = 1) B E hE
    (fun e f => by simpa only [inv_mul_eq_one] using hpair e f)
  have henergy' : (∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2) ≤
      B / (Fintype.card J : ℝ) + E := by
    simpa only [Fintype.card_subtype, Finset.filter_eq', Finset.mem_univ, ite_true,
      Finset.card_singleton, Nat.cast_one, one_div, one_mul, div_eq_mul_inv, mul_comm B] using henergy
  have hCS : ‖∑ x, (μ x : ℂ) * finiteFamilyAverage A x‖ ^ 2 ≤
      (∑ x, μ x) * ∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2 := by
    have hs (x : X) : Real.sqrt (μ x) ^ 2 = μ x := Real.sq_sqrt (hμ x)
    have hp (x : X) : (Real.sqrt (μ x) : ℂ) *
        ((Real.sqrt (μ x) : ℂ) * finiteFamilyAverage A x) = (μ x : ℂ) * finiteFamilyAverage A x := by
      rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, hs]
    have h := complex_pairing_sq_le (fun x : X => (Real.sqrt (μ x) : ℂ))
      (fun x : X => (Real.sqrt (μ x) : ℂ) * finiteFamilyAverage A x)
    simpa only [hp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hs] using h
  rw [hmeanAvg] at hCS
  have hnonneg : 0 ≤ ∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _)
  have hT0 : 0 ≤ T := (Finset.sum_nonneg fun x _ => hμ x).trans hT
  apply hCS.trans
  have hh := mul_le_mul hT henergy' hnonneg hT0
  simpa only [J, card_finalParityReassignments] using hh

end Ostmann

end OAI

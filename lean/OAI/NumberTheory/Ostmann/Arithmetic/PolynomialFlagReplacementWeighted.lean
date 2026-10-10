import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacement

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacement
open scoped BigOperators
open MvPolynomial ProductExpectation

theorem weighted_restricted_flag_error_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (hP : P≠0)
    (S : Fin n → Finset ℤ) (μ : Fin n → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0≤α) (hβ : 0≤β) (hH : 0≤H) (hA : 0≤A)
    (hμ : ∀ i a, a∈S i → 0≤μ i a) (hmass : ∀ i, ∑ a∈S i, μ i a=1)
    (hatom : ∀ i a, a∈S i → μ i a≤α)
    (hprime : ∀ b∈B, b.Prime) (hν : ∀ b∈B,0≤ν b) (hνmass : ∑ b∈B,ν b=1)
    (hνatom : ∀ b∈B,ν b≤β)
    (hsize : ∀ x, (∀ i,x i∈S i) → eval x P≠0 → Real.log |((eval x P:ℤ):ℝ)|≤H)
    (r : (Fin n → ℤ) → ℕ → Bool) (w : (Fin n → ℤ) → ℕ → ℝ)
    (hw : ∀ x, (∀ i,x i∈S i) → ∀ b∈B,0≤w x b ∧ w x b≤A) :
    expectation S μ (fun x => ∑ b∈B,ν b*(if r x b then w x b*flagError P x b else 0)) ≤
      A*((P.totalDegree:ℝ)*α+β*(H/Real.log 2)) := by
  have he : expectation S μ (fun x => ∑ b∈B,ν b*(if r x b then w x b*flagError P x b else 0)) ≤
      expectation S μ (fun x => A*(∑ b∈B,ν b*divisibilityIndicator P x b)) := by
    apply expectation_mono_support S μ hμ
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hp : (if r x b then w x b*flagError P x b else 0) ≤ A*divisibilityIndicator P x b := by
      rw [flagError_of_ne_zero P hP]
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hw x hx b hb).2 (indicator_nonneg P x b)
      · exact mul_nonneg hA (indicator_nonneg P x b)
    have hh := mul_le_mul_of_nonneg_left hp (hν b hb)
    simpa only [mul_assoc,mul_left_comm] using hh
  rw [expectation_const_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (divisibility_probability_le P hP S μ B ν α β H hα hβ hH hμ hmass hatom
      hprime hνmass hνatom hsize) hA)

end Ostmann.Arithmetic.PolynomialFlagReplacement

end

end OAI

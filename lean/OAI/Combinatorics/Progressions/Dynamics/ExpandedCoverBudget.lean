import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean

namespace OAI

section

namespace Erdos3

def expandedCoverBudget (a : ℕ) (P : ℝ) : ℝ := P + (P + a) ^ a

theorem le_expandedCoverBudget (a : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ expandedCoverBudget a P :=
  le_add_of_nonneg_right (pow_nonneg (add_nonneg hP (Nat.cast_nonneg _)) _)

theorem expandedCoverBudget_nonneg (a : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ expandedCoverBudget a P := hP.trans (le_expandedCoverBudget a hP)

theorem shiftedPower_le_expandedCoverBudget (a : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (P + a) ^ a ≤ expandedCoverBudget a P := le_add_of_nonneg_left hP

theorem exists_expandedCoverBudget_absorption (a b : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (expandedCoverBudget a P + b) ^ b ≤ (P + A) ^ A := by
  open Polynomial in
    obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget
      ((X + (X + C a) ^ a + C b) ^ b)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [expandedCoverBudget, Polynomial.eval₂_pow] using hbound P hP

namespace VectorPolynomial

theorem dilateCoefficientFrequency_expanded_bound {K : Type*} {m : ℕ}
    {J : Fin m → Type*} (a q : ℕ) {P : ℝ}
    (hq : (q : ℝ) ≤ Real.exp ((P + a) ^ a))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hfrequency : ∀ j d, d.degree ≤ j.val + 1 → ∀ t,
      |(frequency j d t : ℝ)| ≤ Real.exp P) :
    ∀ j d, d.degree ≤ j.val + 1 → ∀ t,
      |(dilateCoefficientFrequency q frequency j d t : ℝ)| ≤ Real.exp (expandedCoverBudget a P) := by
  intro j d hd t
  apply (dilateCoefficientFrequency_bound q frequency hfrequency j d hd t).trans
  calc
    _ ≤ Real.exp ((P + a) ^ a) * Real.exp P := mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
    _ = Real.exp (expandedCoverBudget a P) := by rw [← Real.exp_add]; congr 1; simp [expandedCoverBudget, add_comm]

end VectorPolynomial
end Erdos3

end

end OAI

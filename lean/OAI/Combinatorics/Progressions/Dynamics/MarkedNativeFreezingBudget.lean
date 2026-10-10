import OAI.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem exists_markedNativeFreezingBudget (s a Cf C₀ C₁ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p →
      p + 1 ≤ (p + C) ^ C ∧
      (markedNativeLiftInput
        (fixedMarkedNativeInput 1 C₀ (fullMarkedNativeInput s a Cf (p + 1))) + C₁) ^ C₁
        ≤ (p + C) ^ C ∧
      (fullMarkedNativeInput s a Cf (p + 1) + C₀) ^ C₀ ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ :=
    2 * (Polynomial.X + 1 + Polynomial.C (s + 3)) ^ (s + 3) +
      ((Polynomial.X + 1 + Polynomial.C (s + 3)) ^ (s + 3)) ^ 2 +
      (Polynomial.X + 1)
  let B : Polynomial ℕ :=
    (Q + Polynomial.C Cf) ^ Cf + (Polynomial.X + 1 + 2) ^ a + Q
  let D : Polynomial ℕ :=
    (B + Polynomial.C C₀) ^ C₀ + (B + 2) ^ (1 : ℕ) + B
  let N : Polynomial ℕ := ((D + 2) ^ 11 + D + Polynomial.C C₁) ^ C₁
  let R : Polynomial ℕ := (B + Polynomial.C C₀) ^ C₀
  let P : Polynomial ℕ := Polynomial.X + 1 + N + R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hp1 : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hn := natPolynomial_eval_nonneg N hp
  have hr := natPolynomial_eval_nonneg R hp
  have hN : N.eval₂ (Nat.castRingHom ℝ) p =
      (markedNativeLiftInput
        (fixedMarkedNativeInput 1 C₀ (fullMarkedNativeInput s a Cf (p + 1))) + C₁) ^ C₁ := by
    simp [N, D, B, Q, Polynomial.eval₂_pow, markedNativeLiftInput,
      fixedMarkedNativeInput, fullMarkedNativeInput, pointwiseFastSectionInput]
  have hR : R.eval₂ (Nat.castRingHom ℝ) p =
      (fullMarkedNativeInput s a Cf (p + 1) + C₀) ^ C₀ := by
    simp [R, B, Q, Polynomial.eval₂_pow, fullMarkedNativeInput, pointwiseFastSectionInput]
  have htotal : p + 1 + N.eval₂ (Nat.castRingHom ℝ) p + R.eval₂ (Nat.castRingHom ℝ) p
      ≤ (p + C) ^ C := by
    simpa only [P, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one]
      using hbudget p hp
  refine ⟨((le_add_of_nonneg_right hn).trans (le_add_of_nonneg_right hr)).trans htotal, ?_, ?_⟩
  · have h := ((le_add_of_nonneg_left hp1).trans (le_add_of_nonneg_right hr)).trans htotal
    simpa only [hN] using h
  · have h := (le_add_of_nonneg_left (add_nonneg hp1 hn)).trans htotal
    simpa only [hR] using h

end Erdos3.NilpotentLieFiltration

end

end OAI

import OAI.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry

namespace OAI

section

namespace Erdos3

open VectorPolynomial RankPreparationFamily

theorem exists_prepared_late_geometry_power_budget
    (s preparationPower requiredPower coordinatePower : ℕ) :
    ∃ latePower : ℕ, 2 ≤ latePower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m : ℕ, m ≤ s → ∀ M : ℕ, (M : ℝ) ≤ (p + 2) ^ coordinatePower →
        ((p + 2) ^ preparationPower + (M : ℝ) +
          (p + 2) ^ (requiredPower + 1) + 2) ^ preparedIntegralBasisExponent m ≤
            (p + 2) ^ latePower := by
  let X : Polynomial ℕ := Polynomial.X
  let A := (X + 2) ^ preparationPower + (X + 2) ^ coordinatePower +
    (X + 2) ^ (requiredPower + 1) + 2
  obtain ⟨latePower, hlate, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (A ^ preparedIntegralBasisExponent s)
  refine ⟨latePower, hlate, ?_⟩
  intro p hp m hm M hM
  have hp0 : 0 ≤ p := by linarith
  have hmono : preparedIntegralBasisExponent m ≤ preparedIntegralBasisExponent s := by
    unfold preparedIntegralBasisExponent
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (preparationExponent_mono hm) 2)
  have hbase : 1 ≤ (p + 2) ^ preparationPower + (M : ℝ) +
      (p + 2) ^ (requiredPower + 1) + 2 := by
    have hprep : 0 ≤ (p + 2) ^ preparationPower := by positivity
    have hrank : 0 ≤ (p + 2) ^ (requiredPower + 1) := by positivity
    have hcap : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  apply (pow_le_pow_right₀ hbase hmono).trans
  apply (pow_le_pow_left₀ (by linarith : 0 ≤ (p + 2) ^ preparationPower + (M : ℝ) +
      (p + 2) ^ (requiredPower + 1) + 2)
    (show (p + 2) ^ preparationPower + (M : ℝ) + (p + 2) ^ (requiredPower + 1) + 2 ≤
      (p + 2) ^ preparationPower + (p + 2) ^ coordinatePower +
        (p + 2) ^ (requiredPower + 1) + 2 by linarith)
    (preparedIntegralBasisExponent s)).trans
  simpa [A, X, Polynomial.eval₂_pow] using hbound p hp0

end Erdos3

end

end OAI

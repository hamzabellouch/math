import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateFailure

namespace OAI

/-! Pointwise norm bounds for the sampled polynomial. These control the
exceptional values when the Fourier approximation is used as a cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma andGateFactor_abs_le {k : ℕ} (S : Finset (Fin k)) (u : Fin k → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ i, |u i| ≤ B) :
    |andGateFactor S u| ≤ 1 + (k : ℝ) * (1 + B) := by
  have hcard : (S.card : ℝ) ≤ k := by
    exact_mod_cast (card_le_card (subset_univ S)).trans_eq (card_fin k)
  calc
    _ ≤ |(1 : ℝ)| + |∑ i ∈ S, (1 - u i)| := abs_sub _ _
    _ ≤ 1 + ∑ i ∈ S, |1 - u i| := by
      simpa only [abs_one] using add_le_add (le_refl (1 : ℝ))
        (abs_sum_le_sum_abs (fun i => 1 - u i) S)
    _ ≤ 1 + ∑ _i ∈ S, (1 + B) := by
      apply add_le_add (le_refl (1 : ℝ))
      apply sum_le_sum
      intro i _
      exact (abs_sub _ _).trans
        (by simpa only [abs_one] using (add_le_add (le_refl (1 : ℝ)) (hu i)))
    _ = 1 + (S.card : ℝ) * (1 + B) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add (le_refl (1 : ℝ))
      (mul_le_mul_of_nonneg_right hcard (by positivity))

lemma sampledAndPolynomial_abs_le {k s : ℕ} (sample : GateSamplingChoices k k s)
    (u : Fin k → ℝ) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ i, |u i| ≤ B) :
    |sampledAndPolynomial sample u| ≤
      (1 + (k : ℝ) * (1 + B)) ^ (s * (Nat.log 2 k + 3)) := by
  calc
    _ = ∏ a : Fin (Nat.log 2 k + 3), ∏ j : Fin s,
        |andGateFactor (sampledCoordinates (sample a j)) u| := by
      simp only [sampledAndPolynomial, abs_prod]
    _ ≤ ∏ _a : Fin (Nat.log 2 k + 3), ∏ _j : Fin s,
        (1 + (k : ℝ) * (1 + B)) := by
      apply prod_le_prod₀
      · intro a _
        exact prod_nonneg (fun _ _ => abs_nonneg _)
      · intro a _
        exact prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun j _ => andGateFactor_abs_le _ u hB hu)
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

end TwoPointCorrelations

end OAI

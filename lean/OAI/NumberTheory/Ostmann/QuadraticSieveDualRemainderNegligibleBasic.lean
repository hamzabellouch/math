import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsPairError
import OAI.NumberTheory.Ostmann.QuadraticSieveDualWindows

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dualSecondErrorScale_le_uniform (M T : ℝ) (Δ K q A : ℕ)
    (hM : 0 < M) (hT : 0 < T) (hq : 0 < q) :
    dualSecondErrorScale M Δ K q A (fun _ _ => T) ≤
      ((2*Δ : ℕ) : ℝ)*(K : ℝ)*Real.sqrt M/T^A := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hD : (((2*Δ).divisors.card : ℕ) : ℝ) ≤ ((2*Δ : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self (2*Δ)
  have hK : (oddSquarefreeUpTo K).card ≤ K := by
    calc
      _ ≤ (Finset.Icc 1 K).card := Finset.card_le_card (fun b hb =>
        Finset.mem_Icc.mpr ⟨(mem_oddSquarefreeUpTo.mp hb).1,
          (mem_oddSquarefreeUpTo.mp hb).2.1⟩)
      _ = _ := by simp
  have hKR : ((oddSquarefreeUpTo K).card : ℝ) ≤ K := by exact_mod_cast hK
  unfold dualSecondErrorScale
  calc
    _ ≤ ∑ _e ∈ (2*Δ).divisors, ∑ _b ∈ oddSquarefreeUpTo K, Real.sqrt M/T^A := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro b hb
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact dual_second_scalar_le hM (by exact_mod_cast Nat.pos_of_mem_divisors he)
        hqR (by exact_mod_cast (mem_oddSquarefreeUpTo.mp hb).1)
    _ = ((2*Δ).divisors.card : ℝ)*((oddSquarefreeUpTo K).card : ℝ)*
        (Real.sqrt M/T^A) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2*Δ : ℕ) : ℝ)*(K : ℝ)*(Real.sqrt M/T^A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hD hKR (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

theorem dualPairErrorScale_le_uniform (S : Finset ℕ) (a : ℕ → ℂ)
    (B : ℕ → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hB : ∀ n ∈ S, ∀ t ∈ S, Nat.Coprime n t → B (n*t) ≤ Q) :
    dualPairErrorScale S a B ≤ (S.card : ℝ)*coefficientEnergy S a*Q := by
  have hc : (∑ n ∈ S, ‖a n‖)^2 ≤ (S.card : ℝ)*coefficientEnergy S a := by
    simpa [coefficientEnergy, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun _ => (1 : ℝ))
  calc
    _ ≤ ∑ n ∈ S, ∑ t ∈ S, ‖a n‖*‖a t‖*Q := by
      unfold dualPairErrorScale
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro t ht
      split_ifs with hcop
      · exact mul_le_mul_of_nonneg_left (hB n hn t ht hcop) (by positivity)
      · positivity
    _ = (∑ n ∈ S, ‖a n‖)^2*Q := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hQ

end Ostmann.QuadraticSieve

end OAI

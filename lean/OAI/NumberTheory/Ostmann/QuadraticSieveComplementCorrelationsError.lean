import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelations

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap

theorem norm_complementaryPair_le (S : Finset ℕ) (a F : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ n ∈ S, ∀ t ∈ S, Nat.Coprime n t → ‖F (n*t)‖ ≤ B) :
    ‖complementaryPair S a F‖ ≤ (S.card : ℝ) * coefficientEnergy S a * B := by
  have hcs : (∑ n ∈ S, ‖a n‖)^2 ≤ (S.card : ℝ) * coefficientEnergy S a := by
    simpa [coefficientEnergy, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun _ => (1 : ℝ))
  calc
    ‖complementaryPair S a F‖ ≤ ∑ n ∈ S, ∑ t ∈ S,
        ‖if Nat.Coprime n t then a n * conj (a t) * F (n*t) else 0‖ := by
      unfold complementaryPair
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => norm_sum_le _ _))
    _ ≤ ∑ n ∈ S, ∑ t ∈ S, ‖a n‖ * ‖a t‖ * B := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro t ht
      by_cases hc : Nat.Coprime n t
      · rw [ite_eq_left hc, norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hF n hn t ht hc) (by positivity)
      · rw [ite_eq_right hc, norm_zero]
        positivity
    _ = (∑ n ∈ S, ‖a n‖)^2 * B := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ (S.card : ℝ) * coefficientEnergy S a * B := mul_le_mul_of_nonneg_right hcs hB

theorem complementaryCorrelation_error (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 0 < M → ∀ (K Δ N : ℕ), Δ ≠ 0 →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      ∀ (X₁ X₂ J L : ℕ → ℝ),
        (∀ v ∈ oddSquarefreeUpTo K,
          0 < X₁ v ∧ X₁ v ≤ Real.sqrt (M/v) ∧ Real.sqrt (M/v) ≤ X₂ v ∧
          0 < J v ∧ J v ≤ min (Real.sqrt (M/v) / X₁ v) (X₂ v / Real.sqrt (M/v)) ∧
          (X₂ v / Real.sqrt (M/v))^2 ≤ L v) →
        ‖complementaryCorrelation W M K Δ S a -
          complementaryCorrelationMain W M K Δ S a X₁ X₂ L‖ ≤
          C * N * coefficientEnergy S a *
            ∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M/v) / J v^A := by
  obtain ⟨C, hC, hbound⟩ := complementaryPoisson_error W A
  refine ⟨C, hC, ?_⟩
  intro M hM K Δ N hΔ S a hS X₁ X₂ J L hp
  have hsum : 0 ≤ ∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M/v) / J v^A := by
    apply Finset.sum_nonneg
    intro v hv
    exact div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hp v hv).2.2.2.1.le _)
  have hcard : S.card ≤ N := by
    calc
      S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card (fun n hn =>
        Finset.mem_Icc.mpr (hS n hn))
      _ = N := by simp
  rw [complementaryCorrelation, complementaryCorrelationMain, ← complementaryPair_sub]
  calc
    _ ≤ (S.card : ℝ) * coefficientEnergy S a *
        (C * ∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M/v) / J v^A) := by
      apply norm_complementaryPair_le S a _ _ (mul_nonneg hC.le hsum)
      intro n hn t ht hcop
      exact hbound M hM K Δ (n*t) hΔ (Nat.mul_pos (hS n hn).1 (hS t ht).1).ne'
        X₁ X₂ J L hp
    _ ≤ (N : ℝ) * coefficientEnergy S a *
        (C * ∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M/v) / J v^A) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC.le hsum)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (coefficientEnergy_nonneg S a)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI

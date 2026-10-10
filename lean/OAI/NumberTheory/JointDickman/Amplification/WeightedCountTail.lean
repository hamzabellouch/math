import OAI.NumberTheory.JointDickman.Counting.TiltedCoefficientTriple

namespace OAI

/-! # Markov bounds for prime counts in the actual coefficient sums -/

namespace JointDickman

open Finset

theorem weighted_exp_markov {α : Type*} (S : Finset α) (w N : α → ℝ) (s r : ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) :
    (∑ x ∈ S, if s * r ≤ s * N x then w x else 0) ≤
      Real.exp (-s * r) * ∑ x ∈ S, w x * Real.exp (s * N x) := by
  classical
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have hwx := hw x hx
  by_cases h : s * r ≤ s * N x
  · rw [ite_eq_left h]
    have he : 1 ≤ Real.exp (-s * r) * Real.exp (s * N x) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    have hh := mul_le_mul_of_nonneg_left he (hw x hx)
    nlinarith
  · rw [ite_eq_right h]
    positivity

noncomputable def tripleCoefficientWeight (B j b c : ℕ) : ℝ :=
  coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c)

noncomputable def triplePrimeCount (k : Fin 3) (Q : Finset ℕ) (j b c : ℕ) : ℝ :=
  primeDivisorCount Q (![b, c, b + j * c] k)

open Filter
open scoped Topology

theorem coefficient_form_exp_moment
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        tripleCoefficientWeight B j b c * Real.exp (s * triplePrimeCount k Q j b c)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
        coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hb⟩ := tilted_coefficient_three_form_with_remainder hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s hs
  have hzero : Real.exp (0 : ℝ) ≤ 2 := by norm_num
  fin_cases k
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q s 0 0 hs hzero hzero
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q 0 s 0 hzero hs hzero
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q 0 0 s hzero hzero hs
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem coefficient_form_count_tail
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (Q : Finset ℕ) (s r : ℝ), Real.exp s ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        if s * r ≤ s * triplePrimeCount k Q j b c then tripleCoefficientWeight B j b c else 0) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (-s * r + ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
        Real.exp (-s * r) * coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_exp_moment hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s r hs
  have hm := weighted_exp_markov ((Ico l₁ r₁) ×ˢ (Ico l₂ r₂))
    (fun bc => tripleCoefficientWeight B j bc.1 bc.2)
    (fun bc => triplePrimeCount k Q j bc.1 bc.2) s r
    (fun bc _ => mul_nonneg (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _))
      (coefficientWeight_nonneg _ _))
  rw [sum_product, sum_product] at hm
  have hh := hm.trans (mul_le_mul_of_nonneg_left
    (hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s hs) (Real.exp_pos _).le)
  apply hh.trans_eq
  rw [Real.exp_add]
  ring

end JointDickman

end OAI

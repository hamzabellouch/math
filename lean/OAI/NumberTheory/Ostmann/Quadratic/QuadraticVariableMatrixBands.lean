import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVariableCorrectionCutoff
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleBandBound

namespace OAI

/-! # Complete variable-cutoff corrections on their actual divisor bands -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_variable_low_band_bound (B N D : ℕ) (hN : 0 < N)
    (P : ℕ → ℕ → Prop) [DecidableRel P]
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0‖ ≤
      3 * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) / N := by
  exact (quadratic_variable_low_correction_weight _ D B P).trans
    (quadratic_sqrt_normalized_gauss_bound (2 * B) N D hN v w hv hw
      K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost)

theorem quadratic_variable_middle_band_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < B → 0 < N → 0 < D →
      ∀ (L : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        if B ≤ b ∧ P d b then
          (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
            quadraticMiddleWindow ρ a ha M e N d v w b L else 0‖ ≤
        ((2 * L + 1) * C * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T)) /
          ((D : ℝ) * Real.sqrt B) := by
  obtain ⟨C, hC, hc⟩ := quadratic_middle_window_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hB hN hD L P _ v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  apply (quadratic_variable_correction_weight _ hD hB P).trans
  have hh := hc M e (2 * B) N D hM he hN L v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        ((2 * L + 1) * C * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem quadratic_variable_small_high_band (E B N D : ℕ)
    (hE : 1 ≤ E) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P] (v w : ℕ → ℂ) (T : ℝ)
    (hbound : (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      T / ((D : ℝ) * Real.sqrt B) := by
  let c : ℝ := 1 / ((D : ℝ) * Real.sqrt B)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        c * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_moebius_root_weight hD hB
            ((Finset.mem_Ioc.mp hd).1.le.trans (le_mul_of_one_le_left (Nat.zero_le d) hE)) h.1)
          (norm_nonneg _)
      · rw [norm_zero]; dsimp [c]; positivity
    _ = c * (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) := by simp only [Finset.mul_sum]
    _ ≤ c * T := mul_le_mul_of_nonneg_left hbound (by dsimp [c]; positivity)
    _ = _ := by dsimp [c]; ring

theorem quadratic_variable_small_middle_band (ρ : 𝓢(ℝ, ℂ)) (M : ℝ)
    (E B N D L : ℕ) (hE : 1 ≤ E) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P] (v w : ℕ → ℂ) (T : ℝ)
    (hbound : (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
            (quadraticSmallScale M b / (E * d : ℕ)) L) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      (((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)) * T := by
  let c : ℝ := ((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg (by positivity) (quadraticSmallFourierBound_nonneg ρ)) (by positivity)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        c * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_small_kernel_fourier_weight ρ _ L hE hD hB
            (Finset.mem_Ioc.mp hd).1.le h.1) (norm_nonneg _)
      · rw [norm_zero]; exact mul_nonneg hc (norm_nonneg _)
    _ = c * (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) := by simp only [Finset.mul_sum]
    _ ≤ c * T := mul_le_mul_of_nonneg_left hbound hc

end Ostmann

end OAI

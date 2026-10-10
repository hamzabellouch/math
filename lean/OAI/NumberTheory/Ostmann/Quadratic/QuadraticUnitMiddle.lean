import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitRoot
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleDivisor

namespace OAI

/-! # The original middle-frequency window including the unit divisor -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_middle_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (l : ℤ), l ≠ 0 → ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound B (2 * N) K₁ → QuadraticSieveBound B (2 * N) K₂ →
      (∑ b ∈ oddSquarefreeRange B, ‖quadraticMiddleDivisor ρ a ha M e N 1 v w b l‖) ≤
        C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_unit_positive_root_gauss_bound (𝓕 (quadraticFourierSquare ρ a ha))
  refine ⟨C, hC, ?_⟩
  intro M e B N hM he hN l hl v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let X := fun b : ℕ => (l.natAbs : ℝ) / 1 * Real.sqrt ((e : ℝ) / (M * b))
  have hX : ∀ b ∈ oddSquarefreeRange B, 0 < X b := by
    intro b hb
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    simpa only [X, Nat.cast_one] using
      quadratic_middle_parameter_pos hM he hb₀ (show 0 < (1 : ℕ) by decide) hl
  have hbound := hc B N X hN hX v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  apply le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_middle_divisor_eq ρ a ha hM he hb₀]
  simp only [X, Nat.cast_one]

theorem quadratic_unit_middle_window_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (L : ℕ) (v w : ℕ → ℂ) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      QuadraticSieveBound B (2 * N) K₁ → QuadraticSieveBound B (2 * N) K₂ →
      (∑ b ∈ oddSquarefreeRange B, ‖quadraticMiddleWindow ρ a ha M e N 1 v w b L‖) ≤
        (2 * L + 1) * C * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_unit_middle_divisor_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N hM he hN L v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  let T := Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
    Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)
  let U := Finset.Icc (-(L : ℤ)) L
  let f := fun (l : ℤ) (b : ℕ) =>
    if l = 0 then (0 : ℝ) else ‖quadraticMiddleDivisor ρ a ha M e N 1 v w b l‖
  have hpoint (l : ℤ) : (∑ b ∈ oddSquarefreeRange B, f l b) ≤ C * T := by
    by_cases hl : l = 0
    · simp only [f, hl, ite_true, Finset.sum_const_zero]
      dsimp [T]; positivity
    · simpa only [f, hl, ite_false] using
        hc M e B N hM he hN l hl v w K₁ K₂ hK₁ hK₂ hv hw h₁ h₂
  have hcard : U.card = 2 * L + 1 := by
    dsimp only [U]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ∑ b ∈ oddSquarefreeRange B, ∑ l ∈ U, f l b := by
      apply Finset.sum_le_sum
      intro b _
      rw [quadratic_middle_window_eq]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = 0 <;> simp [f, hl]
    _ = ∑ l ∈ U, ∑ b ∈ oddSquarefreeRange B, f l b := Finset.sum_comm
    _ ≤ ∑ _l ∈ U, C * T := Finset.sum_le_sum (fun l _ => hpoint l)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

end Ostmann

end OAI

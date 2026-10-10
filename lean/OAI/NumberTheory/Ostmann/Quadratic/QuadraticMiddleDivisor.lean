import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformRootDivisor
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleArgument
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticHybridPoisson

namespace OAI

/-! # The literal middle-frequency correction in the second Poisson formula -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticMiddleDivisor (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b : ℕ) (l : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      v s * conj (w t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ) *
      𝓕 (quadraticFourierSquare ρ a ha)
        ((l : ℝ) * (quadraticSecondScale M e (s * t) b / d))

theorem quadratic_middle_divisor_eq (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e b : ℕ} (hM : 0 < M) (he : 0 < e) (hb : 0 < b)
    (N d : ℕ) (v w : ℕ → ℂ) (l : ℤ) :
    quadraticMiddleDivisor ρ a ha M e N d v w b l =
      quadraticRootGaussDivisor (𝓕 (quadraticFourierSquare ρ a ha))
        ((l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))) N d v w b := by
  unfold quadraticMiddleDivisor quadraticRootGaussDivisor
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [quadratic_middle_frequency_argument ρ a ha hM he hb]

noncomputable def quadraticMiddleWindow (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b L : ℕ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      v s * conj (w t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym (b : ℤ) s : ℂ) * (jacobiSym (b : ℤ) t : ℂ) *
      quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
        (quadraticSecondScale M e (s * t) b / d) L

theorem quadratic_middle_window_eq (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N d : ℕ) (v w : ℕ → ℂ) (b L : ℕ) :
    quadraticMiddleWindow ρ a ha M e N d v w b L =
      ∑ l ∈ Finset.Icc (-(L : ℤ)) L,
        if l = 0 then 0 else quadraticMiddleDivisor ρ a ha M e N d v w b l := by
  unfold quadraticMiddleWindow quadraticLatticeWindow quadraticMiddleDivisor
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l = 0 <;> simp [hl]

theorem quadratic_middle_divisor_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (l : ℤ), l ≠ 0 → ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange B,
        ‖quadraticMiddleDivisor ρ a ha M e N d v w b l‖) ≤
          C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_positive_root_gauss_bound (𝓕 (quadraticFourierSquare ρ a ha))
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hN l hl v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  let X := fun d b : ℕ => (l.natAbs : ℝ) / d * Real.sqrt ((e : ℝ) / (M * b))
  have hX : ∀ d ∈ Finset.Ioc D (2 * D), ∀ b ∈ oddSquarefreeRange B, 0 < X d b := by
    intro d hd b hb
    have hd₀ : 0 < d := lt_of_le_of_lt (Nat.zero_le D) (Finset.mem_Ioc.mp hd).1
    have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    exact quadratic_middle_parameter_pos hM he hb₀ hd₀ hl
  have hbound := hc B N D X hN hX v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  apply le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_middle_divisor_eq ρ a ha hM he hb₀]

theorem quadratic_middle_window_bound (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (e B N D : ℕ), 0 < M → 0 < e → 0 < N →
      ∀ (L : ℕ), ∀ (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound B (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange B,
        ‖quadraticMiddleWindow ρ a ha M e N d v w b L‖) ≤
          (2 * L + 1) * C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_middle_divisor_bound ρ a ha
  refine ⟨C, hC, ?_⟩
  intro M e B N D hM he hN L v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  let S := Finset.Ioc D (2 * D)
  let R := oddSquarefreeRange B
  let U := Finset.Icc (-(L : ℤ)) L
  let f := fun (l : ℤ) (d b : ℕ) =>
    if l = 0 then (0 : ℝ) else ‖quadraticMiddleDivisor ρ a ha M e N d v w b l‖
  have hpoint (l : ℤ) : (∑ d ∈ S, ∑ b ∈ R, f l d b) ≤
      C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
    by_cases hl : l = 0
    · simp only [f, hl, ite_true, Finset.sum_const_zero]
      positivity
    · simpa only [f, hl, ite_false] using
        hc M e B N D hM he hN l hl v w K₁ K₂ T hT hv hw hK₁ hK₂ h₁ h₂ hcost
  have hcard : U.card = 2 * L + 1 := by
    dsimp only [U]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, ∑ l ∈ U, f l d b := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro b _
      rw [quadratic_middle_window_eq]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = 0 <;> simp [f, hl]
    _ = ∑ l ∈ U, ∑ d ∈ S, ∑ b ∈ R, f l d b := by
      conv_lhs =>
        arg 2
        ext d
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ ≤ ∑ _l ∈ U, C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) :=
      Finset.sum_le_sum (fun l _ => hpoint l)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

end Ostmann

end OAI

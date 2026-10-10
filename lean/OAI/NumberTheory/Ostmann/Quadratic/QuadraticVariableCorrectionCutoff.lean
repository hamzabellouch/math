import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOuterBandBounds
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelHighBound

namespace OAI

/-! # Frequency-dependent divisor cutoffs retain the same matrix bounds -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_variable_correction_weight (F : ℕ → ℕ → ℂ) {D B : ℕ}
    (hD : 0 < D) (hB : 0 < B) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F d b else 0‖ ≤
      (1 / ((D : ℝ) * Real.sqrt B)) *
        ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        (1 / ((D : ℝ) * Real.sqrt B)) * ‖F d b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_moebius_root_weight hD hB (Finset.mem_Ioc.mp hd).1.le h.1) (norm_nonneg _)
      · rw [norm_zero]
        positivity
    _ = _ := by simp only [Finset.mul_sum]

theorem quadratic_variable_high_band_bound (B N D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P]
    (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) / ((D : ℝ) * Real.sqrt B) := by
  classical
  apply (quadratic_variable_correction_weight
    (fun d b => quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b) hD hB P).trans
  have hh := quadratic_gauss_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        (3 * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) * (Nat.log 2 (2 * N) + 1) * T)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by push_cast; ring

theorem quadratic_variable_low_correction_weight (F : ℕ → ℕ → ℂ) (D B : ℕ)
    (P : ℕ → ℕ → Prop) [DecidableRel P] :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) * F d b else 0‖ ≤
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · rw [norm_mul]
    have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (norm_nonneg (F d b))
  · simpa only [norm_zero] using norm_nonneg (F d b)

end Ostmann

end OAI

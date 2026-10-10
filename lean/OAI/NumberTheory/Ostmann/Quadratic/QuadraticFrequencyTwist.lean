import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelCharacter
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmoothDivisor
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationBias

namespace OAI

/-! # Absorbing signed square factors into the original coefficient arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticFrequencyTwist (a : ℤ) (c : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if c.Coprime n then (jacobiSym a n : ℂ) * v n else 0

 theorem quadratic_frequency_character (a : ℤ) (c : ℕ) (m : ℤ) {n : ℕ} (hn : n ≠ 0) :
    (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      (if c.Coprime n then (jacobiSym a n : ℂ) else 0) * (jacobiSym m n : ℂ) := by
  rw [show a * (c : ℤ) ^ 2 * m = (c : ℤ) ^ 2 * (a * m) by ring,
    jacobi_square_mul c (a * m) hn]
  by_cases hc : c.Coprime n
  · rw [ite_eq_left hc, ite_eq_left hc, jacobiSym.mul_left, Int.cast_mul]
  · rw [ite_eq_right hc, ite_eq_right hc, Int.cast_zero, zero_mul]

 theorem quadratic_frequency_coeff (a : ℤ) (c : ℕ) (m : ℤ)
    (v : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    v n * (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      quadraticFrequencyTwist a c v n * (jacobiSym m n : ℂ) := by
  rw [quadratic_frequency_character a c m hn]
  unfold quadraticFrequencyTwist
  split_ifs <;> ring

 theorem quadratic_frequency_conj_coeff (a : ℤ) (c : ℕ) (m : ℤ)
    (v : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    conj (v n) * (jacobiSym (a * (c : ℤ) ^ 2 * m) n : ℂ) =
      conj (quadraticFrequencyTwist a c v n) * (jacobiSym m n : ℂ) := by
  simpa only [map_mul, map_intCast] using
    congrArg conj (quadratic_frequency_coeff a c m v hn)

 theorem quadraticFrequencyTwist_norm (a : ℤ) (c : ℕ) (v : ℕ → ℂ) (n : ℕ) :
    ‖quadraticFrequencyTwist a c v n‖ ≤ ‖v n‖ := by
  unfold quadraticFrequencyTwist
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_jacobi_complex_le a n) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp

 theorem quadraticFrequencyTwist_moment (a : ℤ) (c N : ℕ) (v : ℕ → ℂ) :
    quadraticDivisorMoment N (quadraticFrequencyTwist a c v) ≤ quadraticDivisorMoment N v := by
  apply Finset.sum_le_sum
  intro n _
  gcongr
  exact quadraticFrequencyTwist_norm a c v n

 theorem quadraticFrequencyTwist_zero (a : ℤ) (c : ℕ) (v : ℕ → ℂ) {n : ℕ}
    (hn : v n = 0) : quadraticFrequencyTwist a c v n = 0 := by
  simp [quadraticFrequencyTwist, hn]

 theorem quadratic_smooth_gauss_frequency_twist (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (v w : ℕ → ℂ) (a : ℤ) (c : ℕ) (m : ℤ) :
    quadraticSmoothGaussDivisor ρ X N d v w (a * (c : ℤ) ^ 2 * m) =
      quadraticSmoothGaussDivisor ρ X N d
        (quadraticFrequencyTwist a c v) (quadraticFrequencyTwist a c w) m := by
  unfold quadraticSmoothGaussDivisor
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hs0 := (Finset.mem_filter.mp hs).2.2.ne_zero
  have ht0 := (Finset.mem_filter.mp ht).2.2.ne_zero
  have h₁ := quadratic_frequency_coeff a c m v hs0
  have h₂ := quadratic_frequency_conj_coeff a c m w ht0
  calc
    _ = (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        (v s * (jacobiSym (a * (c : ℤ) ^ 2 * m) s : ℂ)) *
        (conj (w t) * (jacobiSym (a * (c : ℤ) ^ 2 * m) t : ℂ)) *
        quadraticGaussMultiplier (s * t) * ρ (X / ((s : ℝ) * t)) := by ring
    _ = _ := by rw [h₁, h₂]; ring

 theorem quadratic_smooth_frequency_twist (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (N d : ℕ) (v w : ℕ → ℂ) (a : ℤ) (c : ℕ) (m : ℤ) :
    quadraticSmoothDivisor ρ X N d v w (a * (c : ℤ) ^ 2 * m) =
      quadraticSmoothDivisor ρ X N d
        (quadraticFrequencyTwist a c v) (quadraticFrequencyTwist a c w) m := by
  unfold quadraticSmoothDivisor
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hs0 := (Finset.mem_filter.mp hs).2.2.ne_zero
  have ht0 := (Finset.mem_filter.mp ht).2.2.ne_zero
  have h₁ := quadratic_frequency_coeff a c m v hs0
  have h₂ := quadratic_frequency_conj_coeff a c m w ht0
  calc
    _ = (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        (v s * (jacobiSym (a * (c : ℤ) ^ 2 * m) s : ℂ)) *
        (conj (w t) * (jacobiSym (a * (c : ℤ) ^ 2 * m) t : ℂ)) *
        ρ (X / ((s : ℝ) * t)) := by ring
    _ = _ := by rw [h₁, h₂]; ring

end Ostmann

end OAI

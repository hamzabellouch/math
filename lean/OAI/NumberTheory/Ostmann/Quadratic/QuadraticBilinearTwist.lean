import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTwist
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSqrtCoefficients
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussBilinear

namespace OAI

/-! # The actual signed frequencies in the full correction matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gauss_bilinear_twist (N₁ N₂ d : ℕ) (v w : ℕ → ℂ) (u m : ℤ) :
    quadraticGaussDivisorBilinear N₁ N₂ d v w (u * m) =
      quadraticGaussDivisorBilinear N₁ N₂ d
        (quadraticFrequencyTwist u 1 v) (quadraticFrequencyTwist u 1 w) m := by
  unfold quadraticGaussDivisorBilinear
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have h₁ := quadratic_frequency_coeff u 1 m v (Finset.mem_filter.mp hs).2.2.ne_zero
  have h₂ := quadratic_frequency_conj_coeff u 1 m w (Finset.mem_filter.mp ht).2.2.ne_zero
  simp only [Nat.cast_one, one_pow, mul_one] at h₁ h₂
  calc
    _ = (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        (v s * (jacobiSym (u * m) s : ℂ)) * (conj (w t) * (jacobiSym (u * m) t : ℂ)) *
          quadraticGaussMultiplier (s * t) := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem quadratic_bilinear_twist (N₁ N₂ d : ℕ) (v w : ℕ → ℂ) (u m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d v w (u * m) =
      quadraticDivisorBilinear N₁ N₂ d
        (quadraticFrequencyTwist u 1 v) (quadraticFrequencyTwist u 1 w) m := by
  unfold quadraticDivisorBilinear
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have h₁ := quadratic_frequency_coeff u 1 m v (Finset.mem_filter.mp hs).2.2.ne_zero
  have h₂ := quadratic_frequency_conj_coeff u 1 m w (Finset.mem_filter.mp ht).2.2.ne_zero
  simp only [Nat.cast_one, one_pow, mul_one] at h₁ h₂
  calc
    _ = (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        (v s * (jacobiSym (u * m) s : ℂ)) * (conj (w t) * (jacobiSym (u * m) t : ℂ)) := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem quadratic_sqrt_twist_commute (u : ℤ) (v : ℕ → ℂ) :
    quadraticFrequencyTwist u 1 (quadraticSqrtNormalize v) =
      quadraticSqrtNormalize (quadraticFrequencyTwist u 1 v) := by
  funext n
  simp [quadraticFrequencyTwist, quadraticSqrtNormalize, div_eq_mul_inv, mul_assoc]

end Ostmann

end OAI

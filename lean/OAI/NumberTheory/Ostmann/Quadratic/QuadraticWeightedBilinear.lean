import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFourierSeparation

namespace OAI

/-! # Smooth logarithmic weights in the literal divisor bilinear form -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

noncomputable def quadraticLogWeightedDivisor (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
      f (Real.log s + Real.log t)

 theorem quadratic_log_modulated_bilinear (N₁ N₂ d : ℕ) (a b : ℕ → ℂ) (m : ℤ) (u : ℝ) :
    quadraticDivisorBilinear N₁ N₂ d (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m =
    ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
      ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
        a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
        realAdditivePhase (u * Real.log s) * realAdditivePhase (u * Real.log t) := by
  unfold quadraticDivisorBilinear quadraticLogModulate
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [map_mul, conj_realAdditivePhase, neg_mul, neg_neg]
  ring

 theorem quadratic_log_weighted_separation (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticLogWeightedDivisor f N₁ N₂ d a b m =
      ∫ u : ℝ, 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m := by
  unfold quadraticLogWeightedDivisor
  rw [quadratic_finite_log_separation]
  apply integral_congr_ae
  filter_upwards with u
  rw [quadratic_log_modulated_bilinear]

 theorem quadratic_log_integrand_integrable (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    Integrable (fun u : ℝ => 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m) := by
  have hi := integrable_finsetSum (oddSquarefreeRange N₁) (fun s _ =>
    integrable_finsetSum (oddSquarefreeRange N₂) (fun t _ =>
      quadratic_log_pair_integrable f
        ((if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
          a s * conj (b t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) s t))
  apply hi.congr
  filter_upwards with u
  rw [quadratic_log_modulated_bilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem quadratic_log_weighted_norm (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticLogWeightedDivisor f N₁ N₂ d a b m‖ ≤
      ∫ u : ℝ, ‖𝓕 f u‖ * ‖quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖ := by
  rw [quadratic_log_weighted_separation]
  simpa only [norm_mul] using norm_integral_le_integral_norm
    (fun u : ℝ => 𝓕 f u * quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m)

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformBilinear
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogFourierEnvelope

namespace OAI

/-! # A common Fourier majorant for frequency-dependent smooth weights -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

 theorem quadratic_varying_weighted_bilinear_bound (f : ℕ → ℕ → 𝓢(ℝ, ℂ))
    (ω : ℝ → ℝ) (hω : Integrable ω) (hω₀ : ∀ u, 0 ≤ ω u) (M N₁ N₂ D : ℕ)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hf : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
      ∀ u : ℝ, ‖𝓕 (f d m) u‖ ≤ ω u)
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d a b m‖) ≤
      (∫ u : ℝ, ω u) *
        (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T) := by
  let G : ℕ → ℕ → ℝ → ℝ := fun d m u => ‖𝓕 (f d m) u‖ *
    ‖quadraticDivisorBilinear N₁ N₂ d
      (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖
  let C : ℝ := ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T
  have hI (d m : ℕ) : Integrable (G d m) := by
    simpa only [G, norm_mul] using (quadratic_log_integrand_integrable (f d m) N₁ N₂ d a b m).norm
  have hsum : Integrable (fun u : ℝ =>
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, G d m u) :=
    integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun m _ => hI d m))
  have hbound (u : ℝ) : (∑ d ∈ Finset.Ioc D (2 * D),
      ∑ m ∈ oddSquarefreeRange M, G d m u) ≤ ω u * C := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ω u * ‖quadraticDivisorBilinear N₁ N₂ d
            (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖ := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hf d hd m hm u) (norm_nonneg _)
      _ = ω u * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ d
            (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖) := by
        simp only [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (quadratic_log_modulated_uniform_bound M N₁ N₂ D a b K₁ K₂ T hT
          hK₁ hK₂ h₁ h₂ hcost u) (hω₀ u)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, ∫ u : ℝ, G d m u := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      exact quadratic_log_weighted_norm (f d m) N₁ N₂ d a b m
    _ = ∑ d ∈ Finset.Ioc D (2 * D), ∫ u : ℝ,
        ∑ m ∈ oddSquarefreeRange M, G d m u := by
      apply Finset.sum_congr rfl
      intro d _
      exact (integral_finsetSum _ (fun m _ => hI d m)).symm
    _ = ∫ u : ℝ, ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M, G d m u :=
      (integral_finsetSum _ (fun d _ =>
        integrable_finsetSum _ (fun m _ => hI d m))).symm
    _ ≤ ∫ u : ℝ, ω u * C :=
      integral_mono hsum (hω.mul_const C) hbound
    _ = _ := integral_mul_const C _

end Ostmann

end OAI

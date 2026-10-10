import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedGaussBound
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVaryingBilinear

namespace OAI

/-! # Varying smooth weights with the actual Gauss coefficient -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

 theorem quadratic_varying_weighted_gauss_bound (f : ℕ → ℕ → 𝓢(ℝ, ℂ))
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
      ‖quadraticLogWeightedGaussDivisor (f d m) N₁ N₂ d a b m‖) ≤
      3 * (∫ u : ℝ, ω u) *
        (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T) := by
  have hc₁ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ (quadraticGaussLeft a)) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ (quadraticGaussRight b)) ≤ T := by
    simpa only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] using hcost
  have hc₂ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁
        (quadraticThreeClass (quadraticGaussLeft a))) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂
          (quadraticThreeClass (quadraticGaussRight b))) ≤ T := by
    intro i hi j hj hlo hhi
    apply le_trans _ (hc₁ i hi j hj hlo hhi)
    gcongr
    · have := hK₁ i hi
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
    · have := hK₂ j hj
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
  have hb₁ := quadratic_varying_weighted_bilinear_bound f ω hω hω₀ M N₁ N₂ D
    (quadraticGaussLeft a) (quadraticGaussRight b) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hc₁
  have hb₂ := quadratic_varying_weighted_bilinear_bound f ω hω hω₀ M N₁ N₂ D
    (quadraticThreeClass (quadraticGaussLeft a))
    (quadraticThreeClass (quadraticGaussRight b)) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hf hc₂
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_log_weighted_gauss_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticLogWeightedDivisor (f d m) N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hb₁, hb₂]

end Ostmann

end OAI

import OAI.NumberTheory.TwoPoint.Fourier.MinorArcFourthExpansion

namespace OAI

/-! The prime fourth moment is controlled by the rational geometric kernel
at the additive differences p₁+p₂-p₃-p₄. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped ComplexConjugate

lemma minor_arc_phase_four (α x₁ x₂ x₃ x₄ : ℝ) (m : ℕ) :
    additiveCharacter (α * x₁) m * additiveCharacter (α * x₂) m *
      conj (additiveCharacter (α * x₃) m) * conj (additiveCharacter (α * x₄) m) =
      additiveCharacter (α * (x₁ + x₂ - x₃ - x₄)) m := by
  simp only [additiveCharacter, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem minor_arc_prime_fourth (P : Finset ℕ) (c : ℕ → ℂ)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ 1) (α : ℝ) (a b : ℕ) :
    (∑ m ∈ Ico a b, ‖∑ p ∈ P, c p * additiveCharacter (α * p) m‖ ^ 4) ≤
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        minorArcGeometricBound ((b - a : ℕ) : ℝ)
          (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  apply (minor_arc_fourth_moment_bound P (Ico a b)
    (fun p m => c p * additiveCharacter (α * p) m)).trans
  apply sum_le_sum
  intro p₁ hp₁
  apply sum_le_sum
  intro p₂ hp₂
  apply sum_le_sum
  intro p₃ hp₃
  apply sum_le_sum
  intro p₄ hp₄
  let d := c p₁ * c p₂ * conj (c p₃) * conj (c p₄)
  have hd : ‖d‖ ≤ 1 := by
    dsimp [d]
    simp only [norm_mul, norm_conj]
    calc
      ‖c p₁‖ * ‖c p₂‖ * ‖c p₃‖ * ‖c p₄‖ ≤ 1 * 1 * 1 * 1 := by
        gcongr <;> first | exact hc _ hp₁ | exact hc _ hp₂ | exact hc _ hp₃ | exact hc _ hp₄
      _ = 1 := by norm_num
  have he : (∑ m ∈ Ico a b,
      (c p₁ * additiveCharacter (α * p₁) m) * (c p₂ * additiveCharacter (α * p₂) m) *
      conj (c p₃ * additiveCharacter (α * p₃) m) *
      conj (c p₄ * additiveCharacter (α * p₄) m)) =
      d * ∑ m ∈ Ico a b, additiveCharacter (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) m := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    rw [← minor_arc_phase_four]
    dsimp [d]
    simp only [map_mul]
    ring
  rw [he, norm_mul]
  calc
    _ ≤ 1 * ‖∑ m ∈ Ico a b, additiveCharacter (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) m‖ :=
      mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using
      minor_arc_geometric_bound (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) a b

end TwoPointCorrelations

end OAI

import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticCollisions
import OAI.NumberTheory.Ostmann.Characters.MellinParseval

namespace OAI

/-!
# A weighted fourth moment of multiplicative character sums

The full character sum selects equality of two nonzero products. Together
with the split-quadratic collision count, this gives equation
`tree-fourth-moment` of the manuscript.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance characterFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem mellin_field_dual_orthogonality {p : ℕ} [Fact p.Prime]
    (x z : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z)) =
      if x = z ∧ x ≠ 0 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  by_cases hz : z = 0
  · simp [hz, MulChar.map_zero]
  have h := mellin_dual_orthogonality (Units.mk0 x hx) (Units.mk0 z hz)
  have heq : (x = z ∧ x ≠ 0) ↔ x = z := and_iff_left hx
  simpa only [Units.val_mk0, Units.mk0_inj, heq] using h

noncomputable def weightedCharacterSum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  ∑ b : ZMod p, (w b : ℂ) * χ (a - b)

theorem weightedCharacterSum_fourth_expansion {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ((‖weightedCharacterSum w χ a‖ ^ 4 : ℝ) : ℂ) =
      ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
        ((w b₁ * w b₂ * w b₃ * w b₄ : ℝ) : ℂ) *
          χ ((a - b₁) * (a - b₂)) * conj (χ ((a - b₃) * (a - b₄))) := by
  have hconj : conj (weightedCharacterSum w χ a) =
      ∑ b : ZMod p, (w b : ℂ) * conj (χ (a - b)) := by
    simp [weightedCharacterSum, map_sum, map_mul]
  calc
    _ = (weightedCharacterSum w χ a * conj (weightedCharacterSum w χ a)) ^ 2 := by
      rw [Complex.mul_conj']
      push_cast
      ring
    _ = (∑ b₁ : ZMod p, (w b₁ : ℂ) * conj (χ (a - b₁))) *
        (∑ b₂ : ZMod p, (w b₂ : ℂ) * conj (χ (a - b₂))) *
        (∑ b₃ : ZMod p, (w b₃ : ℂ) * χ (a - b₃)) *
        (∑ b₄ : ZMod p, (w b₄ : ℂ) * χ (a - b₄)) := by
      rw [hconj]
      unfold weightedCharacterSum
      ring
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      apply Finset.sum_congr rfl
      intro b₃ _
      apply Finset.sum_congr rfl
      intro b₄ _
      simp only [map_mul, Complex.ofReal_mul]
      ring

/-- Character orthogonality leaves exactly the nonzero product collisions. -/
theorem weightedCharacterSum_fourth_character_sum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖weightedCharacterSum w χ a‖ ^ 4) =
      (Fintype.card (ZMod p)ˣ : ℝ) *
        ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
          if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) ∧
              (a - b₁) * (a - b₂) ≠ 0 then w b₁ * w b₂ * w b₃ * w b₄ else 0 := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [weightedCharacterSum_fourth_expansion]
  calc
    _ = ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
        ((w b₁ * w b₂ * w b₃ * w b₄ : ℝ) : ℂ) *
          ∑ χ : MulChar (ZMod p) ℂ,
            χ ((a - b₁) * (a - b₂)) * conj (χ ((a - b₃) * (a - b₄))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₁ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₂ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₃ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₄ _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      simp_rw [mellin_field_dual_orthogonality]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      apply Finset.sum_congr rfl
      intro b₃ _
      apply Finset.sum_congr rfl
      intro b₄ _
      split_ifs <;> push_cast <;> ring

end Ostmann

end OAI

import Mathlib.Data.Finset.Prod
import OAI.NumberTheory.Ostmann.QuadraticCenter.FiniteQuadraticScale

namespace OAI

/-! # The finite phase and scale grids for the quadratic coefficient arrays -/

namespace Ostmann

noncomputable def quadraticParameterGrid (Rmax δ : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (⌊1 / δ⌋₊ + 1)) ×ˢ (Finset.range (⌊Rmax / δ⌋₊ + 1))

noncomputable def quadraticGridPhase (δ : ℝ) (j : ℕ × ℕ) : ℝ := j.1 * δ

noncomputable def quadraticGridScale (δ : ℝ) (j : ℕ × ℕ) : ℝ := 1 + j.2 * δ

theorem quadraticParameterGrid_covers (Rmax δ θ R : ℝ) (hδ : 0 < δ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRmax : R ≤ Rmax) :
    ∃ j ∈ quadraticParameterGrid Rmax δ,
      0 ≤ quadraticGridPhase δ j ∧ quadraticGridPhase δ j ≤ θ ∧
      1 ≤ quadraticGridScale δ j ∧ quadraticGridScale δ j ≤ R ∧
      |θ - quadraticGridPhase δ j| < δ ∧ |R - quadraticGridScale δ j| < δ := by
  let j : ℕ × ℕ := (⌊θ / δ⌋₊, ⌊(R - 1) / δ⌋₊)
  have hR0 : 0 ≤ R - 1 := by linarith
  have hjθ : (j.1 : ℝ) ≤ θ / δ := Nat.floor_le (div_nonneg hθ0 hδ.le)
  have hjR : (j.2 : ℝ) ≤ (R - 1) / δ := Nat.floor_le (div_nonneg hR0 hδ.le)
  have hjθ' : θ / δ < (j.1 : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjR' : (R - 1) / δ < (j.2 : ℝ) + 1 := Nat.lt_floor_add_one _
  have hθlo := (le_div_iff₀ hδ).mp hjθ
  have hRlo := (le_div_iff₀ hδ).mp hjR
  have hθhi := (div_lt_iff₀ hδ).mp hjθ'
  have hRhi := (div_lt_iff₀ hδ).mp hjR'
  refine ⟨j, ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hh : j.1 ≤ ⌊1 / δ⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right hθ1 hδ.le)
      omega
    · apply Finset.mem_range.mpr
      have hh : j.2 ≤ ⌊Rmax / δ⌋₊ := Nat.floor_mono
        (div_le_div_of_nonneg_right (by linarith : R - 1 ≤ Rmax) hδ.le)
      omega
  · dsimp [quadraticGridPhase, quadraticGridScale]
    refine ⟨by positivity, hθlo, ?_, by linarith, ?_, ?_⟩
    · have hh : 0 ≤ (j.2 : ℝ) * δ := by positivity
      linarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith

theorem quadraticParameterGrid_card_le (Rmax δ : ℝ) (hRmax : 0 ≤ Rmax) (hδ : 0 < δ) :
    ((quadraticParameterGrid Rmax δ).card : ℝ) ≤ (1 / δ + 1) * (Rmax / δ + 1) := by
  have ha : (⌊1 / δ⌋₊ : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hb : (⌊Rmax / δ⌋₊ : ℝ) ≤ Rmax / δ := Nat.floor_le (div_nonneg hRmax hδ.le)
  simp only [quadraticParameterGrid, Finset.card_product, Finset.card_range, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  gcongr

end Ostmann

end OAI

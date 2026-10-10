import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateHarmonicDiagonal

namespace OAI

/-! # The numerical counterpart cost for the actual harmonic diagonal -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original giant range and terminal bulk cutoff supply the two
exponential denominators in the harmonic product-fibre bound. -/
theorem moving_harmonic_counterpart_le (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (cg Gmin cb : ℝ)
    (X : ℕ) (y : MovingRegularSlot n r m → ℕ)
    (hX : Real.exp Gmin ≤ (X : ℝ))
    (hy : Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, y i : ℕ) : ℝ)) :
    (Real.exp cg / X) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, y i : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - (2 ^ n : ℕ) * (cb - 1)) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  let K := ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
    (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
      (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)))))
  have hp : 0 < Real.exp Gmin * Real.exp ((2 ^ n : ℕ) * (cb - 1)) := by positivity
  have hden : Real.exp Gmin * Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤
      (X : ℝ) * ((∏ i, y i : ℕ) : ℝ) :=
    mul_le_mul hX hy (Real.exp_nonneg _) (Nat.cast_nonneg _)
  calc
    _ = (Real.exp cg / ((X : ℝ) * ((∏ i, y i : ℕ) : ℝ))) * K := by
      dsimp only [K]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (Real.exp cg / (Real.exp Gmin * Real.exp ((2 ^ n : ℕ) * (cb - 1)))) * K :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (Real.exp_nonneg _) hp hden) hK
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_sub]
      rw [show cg - (Gmin + (2 ^ n : ℕ) * (cb - 1)) =
        cg - Gmin - (2 ^ n : ℕ) * (cb - 1) by ring]
      dsimp only [K]
      ring

end Ostmann

end OAI

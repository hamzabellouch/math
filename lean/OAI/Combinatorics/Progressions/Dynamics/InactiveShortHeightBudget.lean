import OAI.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget

namespace OAI

section

namespace Erdos3

theorem inactiveShortHeightBound_le_exp (h T : ℕ) {γ p t : ℝ}
    (hγ : 0 < γ) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hγp : γ⁻¹ ≤ Real.exp p) (hT : (T : ℝ) ≤ Real.exp t) :
    ((max (2 * inactiveDenominator γ) (integerAxisShortBound h T γ) : ℕ) : ℝ) ≤
      Real.exp (p + 2 + h * (t + 1)) := by
  rw [Nat.cast_max]
  apply max_le
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp (p + 1) := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        exact mul_le_mul htwo (inactiveDenominator_le_exp hγ hp hγp)
          (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg _) (by linarith only [ht])))
  · exact integerAxisShortBound_le_exp h T hγ hp hγp hT

end Erdos3

end

end OAI

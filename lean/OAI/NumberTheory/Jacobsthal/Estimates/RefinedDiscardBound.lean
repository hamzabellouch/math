import OAI.NumberTheory.Jacobsthal.Partitions.SourceLabelCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseCells

theorem refined_discard_bound (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) [NeZero W]
    (S Z gamma : ℝ) (hS : 0 ≤ S) (hZ : 0 < Z)
    (hC : S/Z ≤ (C.card : ℝ)) (hW : (W : ℝ)^2 ≤ Z) (hInv : 1/Z ≤ gamma/8) :
    ((discardedPoints C (refinementLabel a W) (S/Z^3)).card : ℝ) ≤ (gamma/8)*(C.card : ℝ) := by
  have hh := discardedPoints_card_bound C (refinementLabel a W) (S/Z^3) (by positivity)
  rw [refinementLabel_card] at hh
  push_cast at hh
  calc
    _ ≤ (W : ℝ)^2*(S/Z^3) := hh
    _ ≤ Z*(S/Z^3) := mul_le_mul_of_nonneg_right hW (by positivity)
    _ = (1/Z)*(S/Z) := by field_simp
    _ ≤ (1/Z)*(C.card : ℝ) := mul_le_mul_of_nonneg_left hC (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hInv (Nat.cast_nonneg _)

end ErdosInverseRefinement

end

end Erdos970

end OAI

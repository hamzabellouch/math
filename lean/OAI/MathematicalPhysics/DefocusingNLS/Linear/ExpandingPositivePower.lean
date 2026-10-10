import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductDifference
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomial

namespace OAI

/-! # Uniform bounds for positive powers in the expanding Sobolev algebra -/

namespace DefocusingNLS

theorem expandingProduct_one_right (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q : FourierL2) :
    expandingProduct a k L ha ha1 hk hL q (expandingConstant a k L 1) = q := by
  apply expandingTorusFunction_injective a k L ha ha1 hk hL
  ext x
  rw [expandingTorusFunction_product, ContinuousMap.mul_apply,
    expandingConstant_function a k L ha ha1 hk hL, mul_one]

theorem expandingPower_one (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q : FourierL2) :
    expandingPower a k L ha ha1 hk hL q 1 = q := by
  apply expandingTorusFunction_injective a k L ha ha1 hk hL
  ext x
  rw [expandingPower_function, pow_one]

theorem expandingPower_positive_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q : FourierL2) (n : ℕ) :
    ‖expandingPower a k L ha ha1 hk hL q (n + 1)‖ ≤
      expandingAlgebraBound a k ^ n * ‖q‖ ^ (n + 1) := by
  induction n with
  | zero => rw [expandingPower_one]; simp
  | succ n ih =>
    change ‖expandingProduct a k L ha ha1 hk hL q
      (expandingPower a k L ha ha1 hk hL q (n + 1))‖ ≤ _
    calc
      _ ≤ expandingAlgebraBound a k * ‖q‖ *
          ‖expandingPower a k L ha ha1 hk hL q (n + 1)‖ :=
        expandingProduct_norm_le a k L ha ha1 hk hL _ _
      _ ≤ expandingAlgebraBound a k * ‖q‖ *
          (expandingAlgebraBound a k ^ n * ‖q‖ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (expandingAlgebraBound_nonneg a k) (norm_nonneg _))
      _ = _ := by rw [pow_succ, pow_succ ‖q‖]; ring

theorem expandingAnticircularCoefficient_one (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q : FourierL2) :
    expandingAnticircularCoefficient a k L ha ha1 hk hL 1 q =
      expandingPower a k L ha ha1 hk hL q 2 := by
  simp only [expandingAnticircularCoefficient, Nat.cast_one, Nat.reduceSub,
    expandingPower, one_smul, expandingProduct_one_right]


end DefocusingNLS

end OAI

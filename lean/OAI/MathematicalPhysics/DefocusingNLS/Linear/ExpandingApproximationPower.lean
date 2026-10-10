import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximationProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPositivePower

namespace OAI

/-! # Positive powers preserve compact coefficient approximation -/

open Filter Topology

namespace DefocusingNLS

theorem ExpandingCompactApproximation.positivePower (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → FourierL2) (hq : ExpandingCompactApproximation a k ha1 hk L hL q)
    (hqb : ∀ n, ‖q n‖ ≤ M) (p : ℕ) :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingPower a k (L n) ha ha1 hk (hL n) (q n) (p + 1)) := by
  induction p with
  | zero => simpa only [zero_add, expandingPower_one] using hq
  | succ p ih =>
    let B := expandingAlgebraBound a k ^ p * M ^ (p + 1)
    have hpb (n : ℕ) : ‖expandingPower a k (L n) ha ha1 hk (hL n) (q n) (p + 1)‖ ≤ B :=
      (expandingPower_positive_norm_le a k (L n) ha ha1 hk (hL n) (q n) p).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hqb n) (p + 1))
          (pow_nonneg (expandingAlgebraBound_nonneg a k) p))
    exact ExpandingCompactApproximation.mul a k (max M B) ha ha1 hk L hL hLinf q _ hq ih
      (fun n => (hqb n).trans (le_max_left _ _)) (fun n => (hpb n).trans (le_max_right _ _))

end DefocusingNLS

end OAI

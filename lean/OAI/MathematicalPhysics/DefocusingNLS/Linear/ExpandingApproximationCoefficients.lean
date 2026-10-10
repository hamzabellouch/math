import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximationCircular

namespace OAI

/-! # Both actual odd-power coefficients have compact approximations -/

open Filter Topology

namespace DefocusingNLS

theorem expandingOdd_coefficients_compact (a k Q : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → FourierL2) (hq : ExpandingCompactApproximation a k ha1 hk L hL q)
    (hqb : ∀ n, ‖q n‖ ≤ Q) (m : ℕ) (hm : 0 < m) :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingCircularCoefficient a k (L n) ha ha1 hk (hL n) m (q n)) ∧
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingAnticircularCoefficient a k (L n) ha ha1 hk (hL n) m (q n)) := by
  cases m with
  | zero => omega
  | succ m =>
    constructor
    · exact ExpandingCompactApproximation.circular a k Q ha ha1 hk L hL hLinf q hq hqb m
    · cases m with
      | zero => exact ExpandingCompactApproximation.anticircular_one a k Q ha ha1 hk L hL hLinf q hq hqb
      | succ m => exact ExpandingCompactApproximation.anticircular_succ a k Q ha ha1 hk L hL hLinf q hq hqb m

end DefocusingNLS

end OAI

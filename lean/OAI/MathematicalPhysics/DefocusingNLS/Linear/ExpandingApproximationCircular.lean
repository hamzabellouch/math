import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximationPower

namespace OAI

/-! # Compact approximation of the actual two scalar linearization coefficients -/

open Filter Topology

namespace DefocusingNLS

variable (a k M : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
  (q : ℕ → FourierL2) (hq : ExpandingCompactApproximation a k ha1 hk L hL q)
  (hqb : ∀ n, ‖q n‖ ≤ M)

include hLinf hq hqb

theorem ExpandingCompactApproximation.circular (m : ℕ) :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingCircularCoefficient a k (L n) ha ha1 hk (hL n) (m + 1) (q n)) := by
  have hqp := ExpandingCompactApproximation.positivePower a k M ha ha1 hk L hL hLinf q hq hqb m
  have hqc := ExpandingCompactApproximation.conjugate a k ha ha1 hk L hL q hq
  have hqcb (n : ℕ) : ‖fourierConjugate (q n)‖ ≤ M := by simpa only [fourierConjugate_norm] using hqb n
  have hqcp := ExpandingCompactApproximation.positivePower a k M ha ha1 hk L hL hLinf
    (fun n => fourierConjugate (q n)) hqc hqcb m
  let B := expandingAlgebraBound a k ^ m * M ^ (m + 1)
  have hb (n : ℕ) (u : FourierL2) (hu : ‖u‖ ≤ M) :
      ‖expandingPower a k (L n) ha ha1 hk (hL n) u (m + 1)‖ ≤ B :=
    (expandingPower_positive_norm_le a k (L n) ha ha1 hk (hL n) u m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu _)
        (pow_nonneg (expandingAlgebraBound_nonneg a k) _))
  have hp := ExpandingCompactApproximation.mul a k B ha ha1 hk L hL hLinf _ _ hqp hqcp
    (fun n => hb n (q n) (hqb n)) (fun n => hb n (fourierConjugate (q n)) (hqcb n))
  exact ExpandingCompactApproximation.smul a k ha1 hk L hL _ hp (((m + 1 + 1 : ℕ) : ℂ))

theorem ExpandingCompactApproximation.anticircular_one :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingAnticircularCoefficient a k (L n) ha ha1 hk (hL n) 1 (q n)) := by
  simpa only [expandingAnticircularCoefficient_one] using
    ExpandingCompactApproximation.positivePower a k M ha ha1 hk L hL hLinf q hq hqb 1

theorem ExpandingCompactApproximation.anticircular_succ (m : ℕ) :
    ExpandingCompactApproximation a k ha1 hk L hL
      (fun n => expandingAnticircularCoefficient a k (L n) ha ha1 hk (hL n) (m + 2) (q n)) := by
  have hqp := ExpandingCompactApproximation.positivePower a k M ha ha1 hk L hL hLinf q hq hqb (m + 2)
  have hqc := ExpandingCompactApproximation.conjugate a k ha ha1 hk L hL q hq
  have hqcb (n : ℕ) : ‖fourierConjugate (q n)‖ ≤ M := by simpa only [fourierConjugate_norm] using hqb n
  have hqcp := ExpandingCompactApproximation.positivePower a k M ha ha1 hk L hL hLinf
    (fun n => fourierConjugate (q n)) hqc hqcb m
  let B₁ := expandingAlgebraBound a k ^ (m + 2) * M ^ (m + 2 + 1)
  let B₂ := expandingAlgebraBound a k ^ m * M ^ (m + 1)
  have hb₁ (n : ℕ) : ‖expandingPower a k (L n) ha ha1 hk (hL n) (q n) (m + 2 + 1)‖ ≤ B₁ :=
    (expandingPower_positive_norm_le a k (L n) ha ha1 hk (hL n) (q n) (m + 2)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hqb n) _)
        (pow_nonneg (expandingAlgebraBound_nonneg a k) _))
  have hb₂ (n : ℕ) : ‖expandingPower a k (L n) ha ha1 hk (hL n) (fourierConjugate (q n)) (m + 1)‖ ≤ B₂ :=
    (expandingPower_positive_norm_le a k (L n) ha ha1 hk (hL n) (fourierConjugate (q n)) m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hqcb n) _)
        (pow_nonneg (expandingAlgebraBound_nonneg a k) _))
  have hp := ExpandingCompactApproximation.mul a k (max B₁ B₂) ha ha1 hk L hL hLinf _ _ hqp hqcp
    (fun n => (hb₁ n).trans (le_max_left _ _)) (fun n => (hb₂ n).trans (le_max_right _ _))
  have hs := ExpandingCompactApproximation.smul a k ha1 hk L hL _ hp ((m + 2 : ℕ) : ℂ)
  have he : m + 2 - 1 = m + 1 := by omega
  simpa only [expandingAnticircularCoefficient, he] using hs

end DefocusingNLS

end OAI

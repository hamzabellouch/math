import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Model.ContinuityCoboundary
import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233

structure BackgroundBumpData (θ : ℝ) where
  radius : ℕ → ℝ
  bump : ℕ → Circle → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_lt : ∀ n, radius n < 1 / ((n : ℝ) + 1)
  continuous_bump : ∀ n, Continuous (bump n)
  bump_zero : ∀ n, bump n 0 = 1
  bump_bounds : ∀ n x, 0 ≤ bump n x ∧ bump n x ≤ 1
  bump_support : ∀ n, Function.support (bump n) ⊆ Metric.closedBall 0 (radius n)
  disjoint_translates : ∀ n, Pairwise (fun i j : Fin (2 ^ (n + 2)) =>
    Disjoint
      ((fun x : Circle => x + ((i : ℕ) + 1) • (θ : Circle)) ''
        Metric.closedBall 0 (radius n))
      ((fun x : Circle => x + ((j : ℕ) + 1) • (θ : Circle)) ''
        Metric.closedBall 0 (radius n)))
  weighted_support_bound :
    (∑' n, (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (radius n))) ≤ 1 / 2

def backgroundNegative {θ : ℝ} (d : BackgroundBumpData θ) (n : ℕ) (x : Circle) : ℝ :=
  InvariantProjection.Continuity.backwardAverage (Equiv.addRight (θ : Circle))
    (d.bump n) (2 ^ (n + 2)) x

def backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) : ℝ :=
  1 + (∑' n, d.bump n x) - (∑' n, backgroundNegative d n x)

def backgroundTransferSum {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) : ℝ :=
  ∑' n, InvariantProjection.Continuity.backgroundTransfer (Equiv.addRight (θ : Circle))
    (d.bump n) (2 ^ (n + 2)) x

end Invariant233

end

end OAI

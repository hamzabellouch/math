import OAI.Analysis.LipschitzHilbert.Trees.LineGridConditionalBMO
import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleGeometricTail

namespace OAI

/-! Geometric John--Nirenberg tails for the concrete line-cell averages. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert.FiniteLineGrid

theorem mean_oscillation_average_tail (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasMeanOscillationBound f A) {N : ℕ} (hN : N ≤ g.depth) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |g.average g.lineMeasure f N x - g.average g.lineMeasure f 0 x|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  have htail := martingale_terminal_geometric_tail (g.average_martingale g.lineMeasure f) N hA
    (mul_nonneg (Nat.cast_nonneg g.branching) hA.le)
    (g.terminal_mean_oscillation f hf hBMO hN)
    (fun i hi x => by
      simpa only [Real.norm_eq_abs] using
        g.average_jump_le_everywhere f hf hBMO (hi.trans_le hN) x) k
  have hscale : (k : ℝ) * ((g.branching : ℝ) * A + 2 * A) =
      (k : ℝ) * ((g.branching : ℝ) + 2) * A := by ring
  simpa only [hscale, Real.norm_eq_abs] using htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI

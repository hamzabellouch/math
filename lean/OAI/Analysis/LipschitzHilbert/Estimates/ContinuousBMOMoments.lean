import OAI.Analysis.LipschitzHilbert.Estimates.ContinuousBMOTail
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricTailMoments

namespace OAI

/-! Real-power John--Nirenberg moments on an actual interval. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (|f x - integralAverage g.lineMeasure f| ^ p) ∂g.lineMeasure) ≤
      7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
        g.lineMeasure univ := by
  have hmeas : Measurable (fun x => |f x - integralAverage g.lineMeasure f|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  apply geometric_tail_rpow_moment g.lineMeasure _ hmeas (fun _ => abs_nonneg _)
    (mul_pos (by positivity) hA) _ hp
  intro n
  simpa only [mul_assoc] using g.continuous_mean_oscillation_tail hb f hf hc hA hBMO n

end LipschitzHilbert.FiniteLineGrid

end

end OAI

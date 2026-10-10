import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKAdaptiveDerivative

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockRoot_contDiff (N k : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) => skBlockRoot N k p.1 p.2) := by
  have H := parameter_contDiff_at_field
    (spinPressure_paramRegular (blockDimension (Fintype.card (Edge N)) N k)
      (blockInteraction (skInteraction N)) (fun _ => 0)
      (blockMass (Fintype.card (Edge N)) N k)).1 (0:ℝ)
  have HC := H.comp (blockCoefficients_contDiff (N := N) (k := k)
    (fun _ : Fin (Fintype.card (Edge N)) => 1/Real.sqrt (N:ℝ)) 1)
  convert HC using 1
  funext p
  simp only [mul_one_div,one_mul]
  rfl

theorem skAdaptivePressure_continuousOn {N k : ℕ} (β : ℝ)
    {q : ℝ → Fin (k+1) → ℝ} {s : Set ℝ} (hq : ContinuousOn q s) :
    ContinuousOn (fun u => skAdaptivePressure N k β (q u) u) s := by
  have hgap : ContinuousOn (fun u => cumulativeGapMap k (q u)) s :=
    (cumulativeGapMap k).continuous.comp_continuousOn hq
  have hv : ContinuousOn (fun u b => β*Real.sqrt (cumulativeGapMap k (q u) b)) s := by
    apply continuousOn_pi.mpr
    intro b
    exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      ((continuous_apply b).comp_continuousOn hgap))
  have hh : ContinuousOn (fun u : ℝ => β*Real.sqrt (1-u)) s :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.sub continuousOn_id))
  exact ((skBlockRoot_contDiff N k).continuous.comp_continuousOn (hh.prodMk hv)).div_const _

theorem skAdaptiveMean_continuousOn {N k : ℕ} (β : ℝ)
    {q : ℝ → Fin (k+1) → ℝ} {s : Set ℝ} (hq : ContinuousOn q s) :
    ContinuousOn (fun u => skAdaptiveMean N k β u (q u)) s := by
  have hgap := (cumulativeGapMap k).continuous.comp_continuousOn hq
  have hv : ContinuousOn (fun u b => Real.sqrt (cumulativeGapMap k (q u) b)) s := by
    apply continuousOn_pi.mpr
    intro b
    exact Real.continuous_sqrt.comp_continuousOn ((continuous_apply b).comp_continuousOn hgap)
  have hh : ContinuousOn (fun u : ℝ => Real.sqrt (1-u)) s :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub continuousOn_id)
  convert (blockAdaptiveOverlap_contDiff (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) β).continuous.comp_continuousOn
      (hh.prodMk hv) using 1
  funext time
  exact skAdaptiveMean_eq_block N k β time (q time)
end SK.Analytic

end
end

end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarRampMoment
import OAI.Probability.SKBarriers.Hierarchy.WeightedListIntegral

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedList_ramp_square_error (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1 ≤ q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ j, |scalarLevelField w.length (fun i => (w.get i).2.1) j
      (coordinateVector w.length (fun i => (w.get i).2.2))| ≤ B) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)-weightedVariance w| ≤ 6*B^2 := by
  have H := scalarPath_ramp_square_error w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => (w.get i).2.2) (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hspin hB hprefix x
  rw [sum_get_map w (fun p => p.2.2^2)] at H
  have HI := weightedList_integral w (g:=fun p : ℝ × ℝ => p.2^2) hf (continuous_snd.pow 2)
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2) x
  dsimp only [Function.comp_def] at HI
  rw [← HI] at H
  simpa only [weightedVariance, show 4*B^2+2*B^2=6*B^2 by ring] using H

theorem rootGradient_zero_eq_deriv (f : ℝ → ℝ) : rootGradient 0 f=deriv f := rfl

end SK.Analytic

end
end

end OAI

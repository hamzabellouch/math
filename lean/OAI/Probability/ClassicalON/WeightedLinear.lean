import OAI.Probability.ClassicalON.GibbsDerivative

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {w : X → ℝ}

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem weightedMean_const_mul (c : ℝ) (f : X → ℝ) :
    weightedMean μ w (fun x => c*f x)=c*weightedMean μ w f := by
  unfold weightedMean
  simp only [show (fun x => w x*(c*f x))=(fun x => c*(w x*f x)) from by funext; ring,
    integral_const_mul]
  ring

theorem weightedMean_add (hw : Continuous w) {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    weightedMean μ w (fun x => f x+g x)=weightedMean μ w f+weightedMean μ w g := by
  unfold weightedMean
  simp_rw [mul_add]
  have hI : Integrable (fun x => w x*f x) μ := compact_integrable (by fun_prop)
  have hJ : Integrable (fun x => w x*g x) μ := compact_integrable (by fun_prop)
  rw [integral_add hI hJ,add_div]

theorem weightedMean_sum (hw : Continuous w) {E : Type uE} [Fintype E] (f : E → X → ℝ)
    (hf : ∀ e,Continuous (f e)) : weightedMean μ w (fun x => ∑ e,f e x)=
      ∑ e,weightedMean μ w (f e) := by
  unfold weightedMean
  simp_rw [Finset.mul_sum]
  have hI (e : E) : Integrable (fun x => w x*f e x) μ := compact_integrable (by fun_prop)
  rw [integral_finsetSum _ (fun e _ => hI e),Finset.sum_div]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem exponentialMean_const_mul (H : X → ℝ) (c : ℝ) (f : X → ℝ) :
    exponentialMean μ H (fun x => c*f x)=c*exponentialMean μ H f :=
  weightedMean_const_mul μ c f

theorem exponentialMean_sum {E : Type uE} [Fintype E] {H : X → ℝ}
    (hH : Continuous H) (f : E → X → ℝ) (hf : ∀ e,Continuous (f e)) :
    exponentialMean μ H (fun x => ∑ e,f e x)=∑ e,exponentialMean μ H (f e) :=
  weightedMean_sum μ hH.rexp f hf

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem exponentialMean_zero (f : X → ℝ) :
    exponentialMean μ (fun _ => 0) f=∫ x,f x ∂μ := by
  simp [exponentialMean,weightedMean]

end
end ClassicalON

end

end OAI

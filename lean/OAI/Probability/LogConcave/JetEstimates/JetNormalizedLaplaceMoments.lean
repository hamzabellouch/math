import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Appell
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

lemma jet_normalizedLaplace_zero_moments {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (normalizedLaplace μ h) 0=
      ∑s∈l.toFinset.powerset,inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ∫z,(∏i∈l.toFinset\s,inner ℝ (v i) z)*h z ∂μ := by
  rw [jet_normalizedLaplace_zero hμ hh hg v l hl]
  simp only [polynomial,Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [show (fun z => (inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ∏i∈l.toFinset\s,inner ℝ (v i) z)*h z)=
      fun z => inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ((∏i∈l.toFinset\s,inner ℝ (v i) z)*h z) by funext z; ring,
      integral_const_mul]
  · intro s _
    exact ((HasGrowth.const _).mul ((HasGrowth.prod (l.toFinset\s)
      (fun i _ => HasGrowth.linear (innerSL ℝ (v i)))))).mul hg |>.integrable
      (((continuous_const.mul (continuous_finsetProd _
        (fun i _ => continuous_const.inner continuous_id))).mul hh).aestronglyMeasurable) hμ.hasMoments

end LogConcaveSampling.Appell

end

end

end

end OAI

import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling.Appell
open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma dir_log_laplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (v : E) :
    JetCalculus.dir v (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) =
      normalizedLaplace μ (fun z => inner ℝ v z) := by
  funext θ
  have hM := hasFDerivAt_laplace hμ continuous_const (HasGrowth.const (1:ℝ)) θ
  have hd := congrFun (dir_laplace hμ continuous_const (HasGrowth.const (1:ℝ)) v) θ
  simp only [mul_one] at hd
  change (fderiv ℝ (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) θ) v = _
  rw [(hM.log (laplace_one_pos hμ θ).ne').fderiv]
  simp only [smul_apply,smul_eq_mul,normalizedLaplace]
  rw [← hd,JetCalculus.dir,hM.fderiv]

end LogConcaveSampling.Appell

end UpperProof
end
end
end

end OAI

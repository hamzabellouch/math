import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling

lemma eq_gibbs_of_proportional {d : ℕ} {V : Point d → ℝ} {ν : Measure (Point d)}
    [IsProbabilityMeasure ν] {C : ℝ≥0∞}
    (h : ν = C • volume.withDensity (gibbsDensity V)) : ν = gibbs V := by
  have hm := congrArg (fun μ : Measure (Point d) => μ Set.univ) h
  rw [measure_univ, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul] at hm
  have hc : C = (partition V)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hm.symm
  rw [h, hc]
  rfl

end LogConcaveSampling

end LowerProof
end
end
end

end OAI

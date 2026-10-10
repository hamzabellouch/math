import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.LogPartition

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem rotation_logPartition_tail {n : ℕ} (hn : 0 < n) (β θ u : ℝ) (hu : 0 ≤ u) :
    (disorderPairLaw n).real {p | u ≤ logPartition β (rotateDisorder θ p).1-
      logPartition β p.1} ≤ Real.exp (-u^2/(θ^2*β^2*(n:ℝ))) := by
  let v : NNReal := ⟨θ^2*β^2*(n:ℝ)/2,by positivity⟩
  have HS : HasSubgaussianMGF (fun p : Disorder n × Disorder n =>
      logPartition β (rotateDisorder θ p).1-logPartition β p.1) v (disorderPairLaw n) := by
    refine ⟨rotation_exp_integrable hn β θ,fun t => ?_⟩
    apply (rotation_exp_integral_le hn β θ t).trans
    apply Real.exp_le_exp.mpr
    change t^2*θ^2*β^2*((n:ℝ)-1)/4 ≤ (θ^2*β^2*(n:ℝ)/2)*t^2/2
    have H : 0 ≤ t^2*θ^2*β^2 := by positivity
    nlinarith
  convert HS.measure_ge_le hu using 1
  congr 2
  change θ^2*β^2*(n:ℝ) = 2*(θ^2*β^2*(n:ℝ)/2)
  ring

theorem product_event_lower_of_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set X} {E : Set (X × Y)} (hA : MeasurableSet A) (hE : MeasurableSet E)
    {c : ℝ} (hc : 0 ≤ c) (hsec : ∀ x ∈ A, c ≤ ν.real {y | (x,y) ∈ E}) :
    c*μ.real A ≤ (μ.prod ν).real E := by
  have H : ENNReal.ofReal c*μ A ≤ (μ.prod ν) E := by
    rw [Measure.prod_apply hE,← lintegral_indicator_const hA (ENNReal.ofReal c)]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν _)).mpr (hsec x hx)
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have HT := ENNReal.toReal_mono (measure_ne_top (μ.prod ν) E) H
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,measureReal_def] using HT

end SK.Analytic

end
end

end

end OAI

import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! Restoring the terminal visit adds at most one to the counting square
norm. The estimate is independent of the auxiliary positive atomic weights. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def countingSquareNorm {D : Type*} (a : D → ℝ≥0∞) : ℝ≥0∞ :=
  (∑' s, a s ^ 2) ^ (1 / 2 : ℝ)

theorem countingSquareNorm_mono {D : Type*} {a b : D → ℝ≥0∞}
    (h : ∀ s, a s ≤ b s) : countingSquareNorm a ≤ countingSquareNorm b := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_le_tsum (fun s => pow_le_pow_left' (h s) 2)

theorem countingSquareNorm_add_le {D : Type*} [Countable D] (a b : D → ℝ≥0∞) :
    countingSquareNorm (a + b) ≤ countingSquareNorm a + countingSquareNorm b := by
  let : MeasurableSpace D := ⊤
  have h := ENNReal.lintegral_Lp_add_le (μ := Measure.count)
    (p := (2 : ℝ)) (measurable_of_countable a).aemeasurable
    (measurable_of_countable b).aemeasurable (by norm_num)
  simpa only [ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

theorem countingSquareNorm_terminal_le {D X : Type*} (p : D → X)
    (hp : Function.Injective p) (x : X) :
    countingSquareNorm (fun s => if x = p s then 1 else 0) ≤ 1 := by
  classical
  by_cases ht : ∃ t, p t = x
  · obtain ⟨t, ht⟩ := ht
    have he : (fun s => if x = p s then (1 : ℝ≥0∞) else 0) =
        fun s => if s = t then 1 else 0 := by
      funext s
      simp only [← ht, hp.eq_iff, eq_comm]
    simp [he, countingSquareNorm]
  · have he : (fun s => if x = p s then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
      funext s
      rw [ite_eq_right (fun h => ht ⟨s, h.symm⟩)]
    simp [he, countingSquareNorm]

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSingletonClass D] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanVisitCount_codePathLaw_norm (d : PathCodeData X Y)
    (p : D → X) (hp : Function.Injective p) (P : ProbabilityMeasure (BasePathCode d)) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
      countingSquareNorm (fun s => meanCodePreVisits d P (p s)) + 1 := by
  simp_rw [meanVisitCount_codePathLaw]
  exact (countingSquareNorm_add_le _ _).trans
    (add_le_add le_rfl (countingSquareNorm_terminal_le p hp d.target))

theorem meanVisitCount_codePathLaw_budget (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (hp : Function.Injective p)
    (c : D → ℝ≥0∞) (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
      (∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ) ^ (1 / 2 : ℝ) + 1 := by
  apply (meanVisitCount_codePathLaw_norm d p hp P).trans
  apply add_le_add _ le_rfl
  exact ENNReal.rpow_le_rpow
    (meanCodePreVisits_square_budget d hU p c hc0 hct P μ τ q hq hbar) (by norm_num)

end CircleDomainRigidity

end

end OAI

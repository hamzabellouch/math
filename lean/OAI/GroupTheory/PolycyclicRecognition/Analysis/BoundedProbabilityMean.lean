import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! # Bounded profile errors: convergence in probability implies mean convergence -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- The compact profile bounds turn a vanishing bad-event probability into
vanishing mean error, even when the sampling law changes with the scale. -/
theorem bounded_mean_tendsto_zero_of_bad_probabilities
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → ProbabilityMeasure X) (f : ℕ → X → ℝ)
    (hf : ∀ n, Measurable (f n)) {C : ℝ}
    (hbound : ∀ n x, 0 ≤ f n x ∧ f n x ≤ C)
    (hbad : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n : Measure X) {x | ε ≤ f n x}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂(μ n : Measure X)) atTop (𝓝 0) := by
  have hint (n) : Integrable (f n) (μ n : Measure X) :=
    (integrable_const C).mono' (hf n).aestronglyMeasurable
      (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound n x).1]
          using (hbound n x).2))
  have hestimate (n) (ε : ℝ) (hε : 0 < ε) :
      (∫ x, f n x ∂(μ n : Measure X)) ≤
        ε + ((μ n : Measure X) {x | ε ≤ f n x}).toReal * C := by
    let bad := {x | ε ≤ f n x}
    have hb : MeasurableSet bad := isClosed_Ici.measurableSet.preimage (hf n)
    have hi : Integrable (bad.indicator (fun _ => C)) (μ n : Measure X) :=
      (integrable_const C).indicator hb
    calc
      (∫ x, f n x ∂(μ n : Measure X)) ≤
          ∫ x, ε + bad.indicator (fun _ => C) x ∂(μ n : Measure X) := by
        apply integral_mono (hint n) ((integrable_const ε).add hi)
        intro x
        change f n x ≤ ε + bad.indicator (fun _ => C) x
        by_cases hx : x ∈ bad
        · rw [indicator_of_mem hx]
          exact (hbound n x).2.trans (by linarith)
        · rw [indicator_of_notMem hx, add_zero]
          exact (lt_of_not_ge hx).le
      _ = ε + ((μ n : Measure X) bad).toReal * C := by
        rw [integral_add (integrable_const ε) hi, integral_indicator hb]
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
          smul_eq_mul, one_mul, Measure.restrict_apply_univ]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hprob : Tendsto (fun n => ((μ n : Measure X) {x | ε / 2 ≤ f n x}).toReal * C)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.toReal_zero, zero_mul] using
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hbad (ε / 2) (half_pos hε))).mul_const C
  filter_upwards [hprob.eventually (gt_mem_nhds (half_pos hε))] with n hn
  have hnonneg : 0 ≤ ∫ x, f n x ∂(μ n : Measure X) :=
    integral_nonneg (fun x => (hbound n x).1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (hestimate n (ε / 2) (half_pos hε)).trans_lt (by linarith)

end PolycyclicRecognition

end OAI

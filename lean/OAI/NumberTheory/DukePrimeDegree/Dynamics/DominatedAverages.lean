import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-!
# Moving sampling measures in ergodic averages

The sampling measure of a short orbit window can depend on the window.
A uniform density bound is sufficient to pass an L1 error estimate to
all these sampling measures at once, without a pointwise ergodic premise.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma integral_sub_const_le_of_domination
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (C c : ℝ) (hC : 0 ≤ C) (hdom : ν ≤ ENNReal.ofReal C • μ)
    (f : X → ℝ) (hf : Integrable f μ) :
    |(∫ x, f x ∂ν) - c| ≤ C * ∫ x, |f x - c| ∂μ := by
  have hfν : Integrable f ν :=
    (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hdom
  have hdiff : Integrable (fun x => f x - c) μ := hf.sub (integrable_const c)
  have he : (∫ x, f x ∂ν) - c = ∫ x, f x - c ∂ν := by
    rw [integral_sub hfν (integrable_const c)]
    simp
  rw [he]
  calc
    |∫ x, f x - c ∂ν| ≤ ∫ x, |f x - c| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x => f x - c))
    _ ≤ ∫ x, |f x - c| ∂(ENNReal.ofReal C • μ) :=
      integral_mono_measure hdom (ae_of_all _ (fun x => abs_nonneg _))
        (hdiff.abs.smul_measure ENNReal.ofReal_ne_top)
    _ = C * ∫ x, |f x - c| ∂μ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]

/-- An L1 ergodic-average error tends to zero under every sequence of
probability sampling measures with the same density bound. -/
theorem integral_tendsto_of_dominated_sampling
    (μ : Measure X) [IsFiniteMeasure μ]
    (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (C c : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ n, ν n ≤ ENNReal.ofReal C • μ)
    (F : ℕ → X → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hmean : Tendsto (fun n => ∫ x, |F n x - c| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂ν n) atTop (𝓝 c) := by
  have herror : Tendsto (fun n => C * ∫ x, |F n x - c| ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hmean
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds hε)] with n hn
  rw [Real.dist_eq]
  exact (integral_sub_const_le_of_domination μ (ν n) C c hC (hdom n) (F n) (hF n)).trans_lt hn

end DukePrimeDegree

end

end OAI

import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem cdf_tendsto_of_weak {μ : ProbabilityMeasure ℝ} {μs : ℕ → ProbabilityMeasure ℝ}
    (ht : Tendsto μs atTop (𝓝 μ)) {x : ℝ} (hx : (μ : Measure ℝ) {x} = 0) :
    Tendsto (fun n => cdf (μs n : Measure ℝ) x) atTop (𝓝 (cdf (μ : Measure ℝ) x)) := by
  have H := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht
    (show (μ : Measure ℝ) (frontier (Set.Iic x)) = 0 by simpa only [frontier_Iic] using hx)
  simpa only [cdf_eq_real,Measure.real,Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ) (Set.Iic x))).comp H

theorem cdf_L1_tendsto_of_weak {μ : ProbabilityMeasure ℝ} {μs : ℕ → ProbabilityMeasure ℝ}
    (ht : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => ∫ x in Set.Icc (0:ℝ) 1,
      |cdf (μs n : Measure ℝ) x-cdf (μ : Measure ℝ) x|) atTop (𝓝 0) := by
  have hc : Set.Countable {x : ℝ | 0 < (μ : Measure ℝ) {x}} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun x => measurableSet_singleton x)
      (fun _ _ hij => Set.disjoint_singleton.mpr hij)
  have hae : ∀ᵐ x ∂volume, Tendsto (fun n => cdf (μs n : Measure ℝ) x) atTop
      (𝓝 (cdf (μ : Measure ℝ) x)) := by
    filter_upwards [hc.ae_notMem volume] with x hx
    apply cdf_tendsto_of_weak ht
    exact le_antisymm (not_lt.mp hx) bot_le
  have H := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (F := fun n x => |cdf (μs n : Measure ℝ) x-cdf (μ : Measure ℝ) x|)
    (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (fun n => (((monotone_cdf (μs n : Measure ℝ)).measurable.sub
      (monotone_cdf (μ : Measure ℝ)).measurable).abs).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      apply abs_le.mpr
      constructor <;> linarith [cdf_nonneg (μs n : Measure ℝ) x,cdf_nonneg (μ : Measure ℝ) x,
        cdf_le_one (μs n : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x])) (by
      filter_upwards [ae_restrict_of_ae hae] with x hx
      simpa only [sub_self,abs_zero] using (hx.sub_const (cdf (μ : Measure ℝ) x)).abs)
  simpa only [integral_zero] using H

end SK.Analytic

end
end

end

end OAI

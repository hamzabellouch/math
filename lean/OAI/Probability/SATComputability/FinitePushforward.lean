import OAI.Probability.SATComputability.IncidentMasks
import OAI.Probability.SATComputability.PoissonCounts

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem finite_indicator_integrable {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (y : Y) :
    Integrable (fun x => if g x = y then (1 : ℝ) else 0) μ := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun z : Y => if z = y then (1 : ℝ) else 0)).comp hg).aestronglyMeasurable) 1
  filter_upwards [] with x
  dsimp only [Function.comp_def]
  split_ifs <;> norm_num

noncomputable def finitePushforward {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) : FiniteLaw Y where
  weight y := ∫ x, if g x = y then 1 else 0 ∂μ
  nonneg y := integral_nonneg (fun x => by split_ifs <;> norm_num)
  total := by
    rw [← integral_finsetSum _ (fun y _ => finite_indicator_integrable μ g hg y)]
    simp

theorem finitePushforward_expect {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (f : Y → ℝ) :
    (finitePushforward μ g hg).expect f = ∫ x, f (g x) ∂μ := by
  simp only [FiniteLaw.expect, finitePushforward]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun y _ => (finite_indicator_integrable μ g hg y).mul_const (f y))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp

theorem bounded_finite_observable {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (f : Y → ℝ) :
    Integrable (fun x => f (g x)) μ := by
  apply Integrable.of_bound ((measurable_of_countable f).comp hg).aestronglyMeasurable
    (∑ y, |f y|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ (g x))

end FixedClauseThreshold.Computability

end OAI

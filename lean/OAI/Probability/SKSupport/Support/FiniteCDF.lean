import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

def finiteCDF (ν : Measure Time) (t : Time) : ℝ := (ν (Iic t)).toReal

lemma finiteCDF_nonneg (ν : Measure Time) (t : Time) : 0 ≤ finiteCDF ν t := ENNReal.toReal_nonneg

lemma finiteCDF_monotone (ν : Measure Time) [IsFiniteMeasure ν] : Monotone (finiteCDF ν) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Iic_subset_Iic.mpr hab))

lemma finiteCDF_bound (ν : Measure Time) [IsFiniteMeasure ν] (t : Time) : finiteCDF ν t ≤ (ν univ).toReal :=
  ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (subset_univ _))

lemma finiteCDF_integral (ν : Measure Time) (t : Time) :
    finiteCDF ν t=∫ r : Time, (if r ≤ t then (1:ℝ) else 0) ∂ν := by
  have he : (fun r : Time => if r ≤ t then (1:ℝ) else 0)=(Iic t).indicator (fun _ => (1:ℝ)) := by
    funext r
    simp only [Set.indicator_apply,mem_Iic]
  rw [he,integral_indicator measurableSet_Iic]
  simp only [finiteCDF,integral_const,measureReal_def,smul_eq_mul,mul_one,Measure.restrict_apply_univ]

lemma finiteCDF_rightContinuous (ν : Measure Time) [IsFiniteMeasure ν] (t : Time) :
    ContinuousWithinAt (finiteCDF ν) (Ici t) t := by
  change Tendsto (fun u => finiteCDF ν u) (𝓝[Ici t] t) (𝓝 (finiteCDF ν t))
  simp only [finiteCDF_integral]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Time => (1:ℝ))
  · exact Eventually.of_forall (fun u => (measurable_const.piecewise measurableSet_Iic measurable_const).aestronglyMeasurable)
  · exact Eventually.of_forall (fun u => Eventually.of_forall (fun r => by split_ifs <;> norm_num))
  · exact integrable_const _
  · filter_upwards [] with r
    by_cases hrt : r ≤ t
    · simp only [ite_eq_left hrt]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [ite_eq_left (hrt.trans hu)]
    · have htr : t < r := lt_of_not_ge hrt
      simp only [ite_eq_right hrt]
      apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htr)] with u hu
      rw [ite_eq_right (not_le_of_gt hu)]

lemma integrable_extend_of_bounded {f : Time → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) : Integrable (extend f) := by
  have hm : Measurable (extend f) := hf.dite measurable_const measurableSet_Ico
  have hi : Integrable ((Ico (0:ℝ) 1).indicator (fun _ => C)) :=
    (integrableOn_const (C := C) measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : t ∈ Ico (0:ℝ) 1
  · simp only [extend,dite_eq_left ht,Real.norm_eq_abs,indicator_of_mem ht]
    exact hC _
  · simp only [extend,dite_eq_right ht,Real.norm_eq_abs,abs_zero,indicator_of_notMem ht,le_refl]

lemma finiteCDF_integrable (ν : Measure Time) [IsFiniteMeasure ν] : Integrable (extend (finiteCDF ν)) :=
  integrable_extend_of_bounded (finiteCDF_monotone ν).measurable
    (fun t => by rw [abs_of_nonneg (finiteCDF_nonneg ν t)];exact finiteCDF_bound ν t)

end ZeroTemperatureSK

end
end

end OAI

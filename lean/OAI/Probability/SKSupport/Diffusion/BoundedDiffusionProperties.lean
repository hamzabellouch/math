import Mathlib
import OAI.Probability.SKSupport.Diffusion.PicardDiffusion
import OAI.Probability.SKSupport.Diffusion.ProgressiveBrownian
import OAI.Probability.SKSupport.Regularity.IntegralTimeStep

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_measurable_at (ℱ : Filtration ℝ≥0 mΩ) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsProgressive ℱ X) (t : ℝ≥0) : Measurable[ℱ t] (X t) :=
  hX.adapted t

namespace BoundedLipschitzDrift
variable (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)

lemma solution_adapted (t : ℝ≥0) :
    Measurable[Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable) t]
      (b.solution W.driver t) :=
  progressive_measurable_at _ (b.solution_progressive _ W.driver_progressive) t

lemma solution_measurable (t : ℝ≥0) : Measurable (b.solution W.driver t) :=
  (b.solution_adapted W t).mono
    ((Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)).le t) le_rfl

lemma solution_integrable (t : ℝ≥0) : Integrable (b.solution W.driver t) W.law := by
  let := W.isProbability
  have hc : Integrable (b.correction W.driver t) W.law := by
    apply Integrable.of_bound
      ((progressive_joint_measurable _ (b.correction_progressive _ W.driver_progressive)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((b.bound:ℝ)*(t:ℝ))
    exact Eventually.of_forall (b.correction_bound _ W.driver_progressive t)
  have hd : Integrable (W.driver t) W.law :=
    (W.brownian.integrable_eval t).congr (W.driver_indistinguishable.mono (fun _ h => (h t).symm))
  exact hd.add hc

lemma solution_continuous_ae : ∀ᵐ ω ∂W.law, Continuous (fun t => b.solution W.driver t ω) := by
  filter_upwards [W.driver_continuous] with ω hω
  exact b.solution_continuous _ W.driver_progressive hω

def pathDrift (t : ℝ) (ω : Ω) : ℝ :=
  b.f (Real.toNNReal t) (b.solution W.driver (Real.toNNReal t) ω)

lemma pathDrift_measurable : Measurable (fun p : ℝ × Ω => b.pathDrift W p.1 p.2) := by
  have hx := progressive_joint_measurable _ (b.solution_progressive _ W.driver_progressive)
  exact b.measurable.comp
    ((measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk
      (hx.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)))

lemma pathDrift_bound (t : ℝ) (ω : Ω) : |b.pathDrift W t ω| ≤ b.bound := b.bounded _ _

lemma pathDrift_integrable (a c : ℝ) (ω : Ω) :
    IntervalIntegrable (fun t => b.pathDrift W t ω) volume a c := by
  apply (intervalIntegrable_const (c := (b.bound:ℝ))).mono_fun
    ((b.pathDrift_measurable W).comp measurable_prodMk_right).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg b.bound.coe_nonneg] using b.pathDrift_bound W t ω)

def displacement (s t : ℝ) (ω : Ω) : ℝ := ∫ r in s..t, b.pathDrift W r ω

lemma displacement_measurable (s t : ℝ) : Measurable (b.displacement W s t) :=
  measurable_time_integral (b.pathDrift_measurable W) s t

lemma displacement_bound (s t : ℝ) (ω : Ω) :
    |b.displacement W s t ω| ≤ (b.bound:ℝ)*|t-s| :=
  intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => b.pathDrift W r ω) (C := (b.bound:ℝ))
    (fun r _ => b.pathDrift_bound W r ω)

lemma solution_increment (s h : ℝ≥0) : ∀ᵐ ω ∂W.law,
    b.solution W.driver (s+h) ω = b.solution W.driver s ω+
      (W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω := by
  filter_upwards [W.driver_indistinguishable] with ω hω
  rw [b.solution_eq _ W.driver_progressive (s+h),b.solution_eq _ W.driver_progressive s,hω,hω]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (b.pathDrift_integrable W 0 s ω) (b.pathDrift_integrable W s (s+h) ω)
  change (∫ r in (0:ℝ)..(s:ℝ), b.pathDrift W r ω)+b.displacement W s (s+h) ω =
    ∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), b.pathDrift W r ω at he
  change W.B (s+h) ω+(∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), b.pathDrift W r ω) =
    W.B s ω+(∫ r in (0:ℝ)..(s:ℝ), b.pathDrift W r ω)+(W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω
  rw [← he]
  ring

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI

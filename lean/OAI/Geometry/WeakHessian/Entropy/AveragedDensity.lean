import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatProbability
import OAI.Geometry.WeakHessian.Entropy.CompressedDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

 def timeAverageLaw (π : Measure (Curve X)) (ν : Measure ℝ) (s : ℝ) : Measure X :=
  (ν.prod π).map (fun z : ℝ × Curve X => evalReal z.2 (s-z.1))

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_timeAverageEval (s : ℝ) :
    Continuous (fun z : ℝ × Curve X => evalReal z.2 (s-z.1)) :=
  continuous_evalReal.comp (continuous_snd.prodMk (continuous_const.sub continuous_fst))

omit [SigmaFinite m] in
lemma IsTestPlan.timeAverageLaw_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    timeAverageLaw π ν s ≤ (B : ℝ≥0∞) • m := by
  let : IsProbabilityMeasure π := hπ.1
  apply Measure.le_iff.mpr
  intro S hS
  rw [timeAverageLaw,Measure.map_apply (continuous_timeAverageEval s).measurable hS,
    Measure.prod_apply (hS.preimage (continuous_timeAverageEval s).measurable)]
  calc
    _ ≤ ∫⁻ _r, ((B : ℝ≥0∞) • m) S ∂ν := by
      apply lintegral_mono
      intro r
      simpa only [Measure.map_apply (continuous_eval_const (clampTime (s-r))).measurable hS,
        preimage_preimage,Function.comp_def,evalReal] using (hB (clampTime (s-r))) S
    _ = _ := by simp

lemma isProbabilityMeasure_timeAverageLaw (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    IsProbabilityMeasure (timeAverageLaw π ν s) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_timeAverageEval s).measurable.aemeasurable).mpr inferInstance

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma integrable_shiftedDensity {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun r => u (clampTime (s-r))) ν := by
  apply Integrable.of_bound
    ((hu.comp_measurable (continuous_clampTime.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable)
    ((B : ℝ)+1)
  filter_upwards [] with r
  change ‖u (clampTime (s-r))‖ ≤ (B : ℝ)+1
  have hb := hB (clampTime (s-r))
  have hn := norm_nonneg (u (clampTime (s-r)))
  have hB0 := B.coe_nonneg
  nlinarith [sq_nonneg (‖u (clampTime (s-r))‖-1)]

omit [SigmaFinite m] in
lemma timeAverageLaw_density_pairing
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) (f : Lp ℝ 2 m) :
    (∫ x, f x ∂timeAverageLaw π ν s) = ∫ r, ⟪f,u (clampTime (s-r))⟫_ℝ ∂ν := by
  let : IsProbabilityMeasure π := hπ.1
  let := isProbabilityMeasure_timeAverageLaw π ν s
  have hle := hπ.timeAverageLaw_le hB ν s
  have hf : Integrable f (timeAverageLaw π ν s) :=
    MemLp.integrable (by norm_num) (((Lp.memLp f).smul_measure ENNReal.coe_ne_top).mono_measure hle)
  have hprod : Integrable (fun z : ℝ × Curve X => f (evalReal z.2 (s-z.1))) (ν.prod π) :=
    (integrable_map_measure hf.1 (continuous_timeAverageEval s).measurable.aemeasurable).mp hf
  rw [timeAverageLaw,integral_map (continuous_timeAverageEval s).measurable.aemeasurable hf.1,
    integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← integral_densityMeasure_L2 _ _ (hun (clampTime (s-r))),hlaw]
  exact (integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
    ((Lp.memLp f).aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))).symm

lemma IsTestPlan.exists_timeAverageDensity
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    let w := ∫ r, u (clampTime (s-r)) ∂ν
    (∀ᵐ x ∂m, 0 ≤ w x) ∧ (∀ᵐ x ∂m, |w x| ≤ B) ∧
      Integrable w m ∧ (∫ x, w x ∂m) = 1 ∧
      densityMeasure m w = timeAverageLaw π ν s ∧ ‖w‖^2 ≤ (B : ℝ) := by
  let : IsProbabilityMeasure π := hπ.1
  let := isProbabilityMeasure_timeAverageLaw π ν s
  obtain ⟨w,hwn,hwb,hwi,hwm,hwl,hwnorm⟩ := exists_compressedDensity (hπ.timeAverageLaw_le hB ν s)
  have he : (∫ r, u (clampTime (s-r)) ∂ν) = w := by
    apply ext_inner_left ℝ
    intro f
    change (innerSL ℝ f) (∫ r, u (clampTime (s-r)) ∂ν) = ⟪f,w⟫_ℝ
    rw [← (innerSL ℝ f).integral_comp_comm (integrable_shiftedDensity hu hnorm ν s),
      ← integral_densityMeasure_L2 _ _ hwn,hwl]
    exact (timeAverageLaw_density_pairing hπ hB hun hlaw ν s f).symm
  dsimp only
  rw [he]
  refine ⟨hwn,hwb,hwi,?_,hwl,?_⟩
  · simpa [Measure.real] using hwm
  · simpa [Measure.real] using hwnorm

end WeakHessian

end
end

end OAI

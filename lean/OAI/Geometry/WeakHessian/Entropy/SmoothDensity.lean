import Mathlib
import OAI.Geometry.WeakHessian.Entropy.AveragedDensity

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

omit [SigmaFinite m] in
lemma timeAverageLaw_integral
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) {f : X → ℝ} (hf : Integrable f m) :
    (∫ x, f x ∂timeAverageLaw π ν s) =
      ∫ r, (∫ x, u (clampTime (s-r)) x*f x ∂m) ∂ν := by
  let : IsProbabilityMeasure π := hπ.1
  have hle := hπ.timeAverageLaw_le hB ν s
  have hfi : Integrable f (timeAverageLaw π ν s) :=
    (hf.smul_measure ENNReal.coe_ne_top).mono_measure hle
  have hprod : Integrable (fun z : ℝ × Curve X => f (evalReal z.2 (s-z.1))) (ν.prod π) :=
    (integrable_map_measure hfi.1 (continuous_timeAverageEval s).measurable.aemeasurable).mp hfi
  rw [timeAverageLaw,integral_map (continuous_timeAverageEval s).measurable.aemeasurable hfi.1,
    integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← integral_densityMeasure _ _ (hun _),hlaw]
  exact (integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
    (hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))).symm

 def kernelMeasure (κ : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun r => ENNReal.ofReal (κ r))

lemma kernelMeasure_probability {κ : ℝ → ℝ} (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) : IsProbabilityMeasure (kernelMeasure κ) := by
  constructor
  rw [kernelMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn),hm]
  simp

lemma integral_kernelMeasure {κ : ℝ → ℝ} (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ r, f r ∂kernelMeasure κ) = ∫ r, κ r • f r := by
  rw [kernelMeasure,integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _)]

 def smoothDensity (κ : ℝ → ℝ) (u : Time → Lp ℝ 2 m) : ℝ → Lp ℝ 2 m :=
  convolution κ (fun t => u (clampTime t)) (ContinuousLinearMap.lsmul ℝ ℝ)

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_eq_average {κ : ℝ → ℝ} (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r)
    (u : Time → Lp ℝ 2 m) (s : ℝ) :
    smoothDensity κ u s = ∫ r, u (clampTime (s-r)) ∂kernelMeasure κ := by
  rw [integral_kernelMeasure hc hn]
  rfl

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma locallyIntegrable_clampedDensity {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ)) :
    LocallyIntegrable (fun t => u (clampTime t)) := by
  rw [locallyIntegrable_iff]
  intro S hS
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  apply Integrable.of_bound (hu.comp_measurable continuous_clampTime.measurable).aestronglyMeasurable
    ((B : ℝ)+1)
  filter_upwards [] with r
  change ‖u (clampTime r)‖ ≤ (B : ℝ)+1
  have hb := hB (clampTime r)
  have hn := norm_nonneg (u (clampTime r))
  have hB0 := B.coe_nonneg
  nlinarith [sq_nonneg (‖u (clampTime r)‖-1)]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_hasDerivAt {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ)) (s : ℝ) :
    HasDerivAt (smoothDensity κ u) (smoothDensity (deriv κ) u s) s :=
  hκ.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hc
    (locallyIntegrable_clampedDensity hu hB) s

lemma IsTestPlan.smoothDensity_properties
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hc : Continuous κ) (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) :
    (∀ᵐ x ∂m, 0 ≤ smoothDensity κ u s x) ∧
      (∀ᵐ x ∂m, |smoothDensity κ u s x| ≤ B) ∧
      Integrable (smoothDensity κ u s) m ∧ (∫ x, smoothDensity κ u s x ∂m) = 1 ∧
      densityMeasure m (smoothDensity κ u s) = timeAverageLaw π (kernelMeasure κ) s ∧
      ‖smoothDensity κ u s‖^2 ≤ (B : ℝ) := by
  let := kernelMeasure_probability hi hn hm
  rw [smoothDensity_eq_average hc hn]
  exact hπ.exists_timeAverageDensity hB hu hun hlaw hnorm (kernelMeasure κ) s

lemma IsTestPlan.smoothDensity_energy
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hc : Continuous κ) (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ)
    {f : X → ℝ} (hf : Integrable f m) :
    (∫ x, smoothDensity κ u s x*f x ∂m) =
      ∫ r, κ r*(∫ x, u (clampTime (s-r)) x*f x ∂m) := by
  let := kernelMeasure_probability hi hn hm
  obtain ⟨hsn,_,_,_,hsl,_⟩ := hπ.smoothDensity_properties hB hu hun hlaw hnorm hc hi hn hm s
  rw [← integral_densityMeasure _ _ hsn,hsl,
    timeAverageLaw_integral hπ hB hun hlaw (kernelMeasure κ) s hf,integral_kernelMeasure hc hn]
  rfl

end WeakHessian

end
end

end OAI

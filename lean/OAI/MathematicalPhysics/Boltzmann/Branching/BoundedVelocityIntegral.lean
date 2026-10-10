import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteDepthKernelOrder
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace OAI

section

/-! # Absolute entropy for bounded densities with bounded velocity support -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem bounded_velocity_integrable {μ : Measure X} [IsFiniteMeasure μ] {N A : ℝ}
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfb : ∀ p, |f p| ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) : Integrable f (μ.prod (volume : Measure Velocity)) := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  apply (hi.comp_snd μ).mono' hfm.aestronglyMeasurable
  filter_upwards [] with p
  change ‖f p‖ ≤ (Metric.closedBall (0 : Velocity) N).indicator (fun _ => A) p.2
  by_cases hp : p.2 ∈ Metric.closedBall 0 N
  · rw [indicator_of_mem hp,Real.norm_eq_abs]
    exact hfb p
  · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
    rw [hfs p hv,norm_zero,indicator_of_notMem hp]

theorem bounded_velocity_finiteEntropy {N A : ℝ} (hN : 0 ≤ N) {f : Density}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) : FiniteEntropyDatum f := by
  have hi : Integrable f (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact bounded_velocity_integrable hfm (fun p => (abs_of_nonneg (hfn p)).trans_le (hfb p)) hfs
  have hEm : Measurable (fun p : Phase => ‖p.2‖^2*f p) :=
    (measurable_snd.norm.pow_const 2).mul hfm
  have hEi : Integrable (fun p : Phase => ‖p.2‖^2*f p) := by
    rw [Measure.volume_eq_prod]
    apply bounded_velocity_integrable (A := N^2*A) hEm
    · intro p
      by_cases hp : N < ‖p.2‖
      · rw [hfs p hp,mul_zero,abs_zero]
        have hA : 0 ≤ A := (hfn p).trans (hfb p)
        positivity
      · rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hfn p))]
        have hs : ‖p.2‖^2 ≤ N^2 := (sq_le_sq₀ (norm_nonneg _) hN).mpr (le_of_not_gt hp)
        exact mul_le_mul hs (hfb p) (hfn p) (sq_nonneg N)
    · intro p hp
      rw [hfs p hp,mul_zero]
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) A)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlog : Integrable (fun p : Phase => f p*Real.log (f p)) := by
    rw [Measure.volume_eq_prod]
    exact bounded_velocity_integrable (Real.continuous_mul_log.measurable.comp hfm)
      (fun p => by simpa only [Real.norm_eq_abs] using hB (f p) ⟨hfn p,hfb p⟩)
      (fun p hp => by rw [hfs p hp,zero_mul])
  refine ⟨Filter.Eventually.of_forall hfn,hfm.aestronglyMeasurable,?_⟩
  apply ((hi.add hEi).add hlog.norm).congr
  filter_upwards [] with p
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hfn p),entropyMoment]
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # Velocity fibers of bounded supported densities -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness

theorem bounded_velocity_fiber_integrable {N A : ℝ} {f : Velocity → ℝ}
    (hfm : Measurable f) (hfb : ∀ v, |f v| ≤ A)
    (hfs : ∀ v, N < ‖v‖ → f v = 0) : Integrable f := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with v
  by_cases hv : v ∈ Metric.closedBall 0 N
  · rw [indicator_of_mem hv,Real.norm_eq_abs]
    exact hfb v
  · have hNv : N < ‖v‖ := by
      simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hv
    rw [hfs v hNv,norm_zero,indicator_of_notMem hv]

theorem bounded_velocity_fiber_weighted {N A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    {f ψ : Velocity → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hfb : ∀ v, |f v| ≤ A) (hfs : ∀ v, N < ‖v‖ → f v = 0)
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) : Integrable (fun v => ψ v*f v) := by
  apply bounded_velocity_fiber_integrable (N := N) (A := C*A) (hψm.mul hfm)
  · intro v
    change |ψ v*f v| ≤ C*A
    by_cases hv : N < ‖v‖
    · rw [hfs v hv,mul_zero,abs_zero]
      exact mul_nonneg hC hA
    · rw [abs_mul]
      exact mul_le_mul (hψ v (le_of_not_gt hv)) (hfb v) (abs_nonneg _) hC
  · intro v hv
    change ψ v*f v = 0
    rw [hfs v hv,mul_zero]

end BoltzmannNonuniqueness

end

end

section

/-! # An explicit integral bound for compact velocity support -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem bounded_velocity_integral_bound {μ : Measure X} [IsFiniteMeasure μ] {N A : ℝ}
    {f : X × Velocity → ℝ} (hfb : ∀ p, |f p| ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    |∫ p, f p ∂μ.prod volume| ≤
      μ.real univ*(volume : Measure Velocity).real (Metric.closedBall 0 N)*A := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have h := norm_integral_le_of_norm_le (hi.comp_snd μ) (show ∀ᵐ p ∂μ.prod volume,
      ‖f p‖ ≤ (Metric.closedBall (0 : Velocity) N).indicator (fun _ => A) p.2 from by
    filter_upwards [] with p
    by_cases hp : p.2 ∈ Metric.closedBall 0 N
    · rw [indicator_of_mem hp,Real.norm_eq_abs]; exact hfb p
    · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [hfs p hv,norm_zero,indicator_of_notMem hp])
  rw [Real.norm_eq_abs,integral_fun_snd,integral_indicator Metric.isClosed_closedBall.measurableSet,
    setIntegral_const,smul_eq_mul,smul_eq_mul] at h
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness

end

end

end OAI

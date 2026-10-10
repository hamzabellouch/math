import Mathlib
import OAI.Analysis.Conductivity.Fourier.LinearPhaseDerivativeIntegralBound
import OAI.Analysis.Conductivity.Variational.TransitionMajorant

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

theorem periodic_averaging_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (h : SmoothScalar ℝ) (hper : Function.Periodic h.val 1) :
    Tendsto (fun n : ℕ => ∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ)
      atTop (𝓝 ((∫ t in (0 : ℝ)..1, h.val t) * ∫ x, f.val x ∂μ)) := by
  let m : ℝ := ∫ t in (0 : ℝ)..1, h.val t
  let g : SmoothScalar ℝ := h - algebraMap ℝ (SmoothScalar ℝ) m
  have hg : Function.Periodic g.val 1 := by
    intro t
    change h.val (t + 1) - m = h.val t - m
    rw [hper t]
  have hm : (∫ t in (0 : ℝ)..1, g.val t) = 0 := by
    change (∫ t in (0 : ℝ)..1, h.val t - m) = 0
    rw [intervalIntegral.integral_sub ((smoothScalar_contDiff h).continuous.intervalIntegrable _ _)
      intervalIntegrable_const]
    simp [m]
  have hi : Integrable f.val μ := (smoothScalar_contDiff f).continuous.integrable_of_hasCompactSupport hf
  have he (n : ℕ) : (∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ) =
      (∫ x, f.val x * g.val ((n + 1 : ℝ) * L x) ∂μ) + m * ∫ x, f.val x ∂μ := by
    have hi' : Integrable (fun x => f.val x * h.val ((n + 1 : ℝ) * L x)) μ :=
      ((smoothScalar_contDiff f).continuous.mul
        ((smoothScalar_contDiff h).continuous.comp (continuous_const.mul L.continuous))).integrable_of_hasCompactSupport (hf.mul_right)
    change _ = (∫ x, f.val x * (h.val ((n + 1 : ℝ) * L x) - m) ∂μ) + _
    simp_rw [mul_sub]
    rw [integral_sub hi' (hi.mul_const m), integral_mul_const]
    ring
  simp_rw [he]
  simpa only [zero_add] using (periodic_oscillations_weak μ L hL f hf g hg hm).add_const
    (m * ∫ x, f.val x ∂μ)

theorem eventually_impure_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val) (hfn : ∀ x, 0 ≤ f.val x)
    (S : Set E) (hS : ∀ x ∈ S, 1 ≤ f.val x)
    {θ δ ε : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ) (hw : θ + δ ≤ 1)
    (hδw : 3 * δ ≤ 1) (hε : 4 * δ * (∫ x, f.val x ∂μ) < ε) :
    ∀ᶠ n : ℕ in atTop,
      μ {x | x ∈ S ∧ periodicPulse θ δ ((n + 1 : ℝ) * L x) ≠ 0 ∧
        periodicPulse θ δ ((n + 1 : ℝ) * L x) ≠ 1} ≤ ENNReal.ofReal ε := by
  let H : SmoothScalar ℝ := ⟨transitionMajorant θ δ, transitionMajorant_smooth hδ⟩
  have ht := periodic_averaging_smooth μ L hL f hf H (transitionMajorant_periodic θ δ)
  change Tendsto _ _ (𝓝 ((∫ t in (0 : ℝ)..1, transitionMajorant θ δ t) * ∫ x, f.val x ∂μ)) at ht
  rw [transitionMajorant_integral hδ hδw] at ht
  filter_upwards [ht.eventually_lt_const hε] with n hn
  have hi : Integrable (fun x => f.val x * transitionMajorant θ δ ((n + 1 : ℝ) * L x)) μ :=
    ((smoothScalar_contDiff f).continuous.mul
      ((transitionMajorant_smooth hδ).continuous.comp (continuous_const.mul L.continuous))).integrable_of_hasCompactSupport (hf.mul_right)
  apply (hi.measure_le_integral (ae_of_all μ (fun x => mul_nonneg (hfn x)
    (transitionMajorant_bounds hδ hδw _).1)) ?_).trans (ENNReal.ofReal_le_ofReal hn.le)
  intro x hx
  calc
    1 = 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul (hS x hx.1) (transitionMajorant_dominates hδ hδθ hw hδw hx.2.1 hx.2.2) (by norm_num) (by linarith [hS x hx.1])

end ScalarConductivity

end

end OAI

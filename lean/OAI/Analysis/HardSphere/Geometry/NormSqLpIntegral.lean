import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re]
  · apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,inner_self_eq_norm_sq]
  · exact L2.integrable_inner _ _

lemma bounded_toLp_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → ℂ} {f : α → ℂ} (hF : ∀ t, MemLp (F t) 2 μ) (hf : MemLp f 2 μ)
    {C : ℝ} (_hC : 0≤C) (hFb : ∀ t x, ‖F t x‖≤C) (hfb : ∀ x, ‖f x‖≤C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun t ↦ F t x) l (𝓝 (f x))) :
    Tendsto (fun t ↦ (hF t).toLp (F t)) l (𝓝 (hf.toLp f)) := by
  have H : Tendsto (fun t ↦ ∫ x, ‖F t x-f x‖^2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (2*C)^2)
      (l := l) (F := fun t x ↦ ‖F t x-f x‖^2) (f := fun _ ↦ (0:ℝ))
      (Eventually.of_forall fun t ↦ ((hF t).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2)
      (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hFb t x,hfb x]))
      (integrable_const _) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ht] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hsq : ∀ t, (dist ((hF t).toLp (F t)) (hf.toLp f))^2=
      ∫ x, ‖F t x-f x‖^2 ∂μ := by
    intro t
    rw [dist_eq_norm,← MemLp.toLp_sub (hF t) hf]
    exact norm_sq_toLp_eq_integral _
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp H
  simpa only [Function.comp_def,← hsq,Real.sqrt_sq (dist_nonneg),Real.sqrt_zero] using hroot

end HardSphere

end

end OAI

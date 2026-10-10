import Mathlib
import OAI.Probability.SKValue.Equations.RealFiltration

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma UnitMomentMartingale.weighted_terminal_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {γ : ℝ → ℝ} {T : ℝ} (hT : 0≤T) (hT1 : T<1)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T))
    (hγ : IntervalIntegrable γ volume 0 T) :
    (∫ ω, U ω*(∫ t in (0 : ℝ)..T, γ t*f t ω) ∂μ)=∫ t in (0 : ℝ)..T, t*γ t := by
  have hm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : t∈Ico (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT1⟩
  rw [compact_weighted_fubini hT (fun t ht ↦ (h.measurable t (hm t ht)).mono (ℱ.le t))
    hc (fun t ht ↦ h.bounded t (hm t ht)) (hUm.mono (ℱ.le 1)).aestronglyMeasurable
    (hU.mono (fun _ hω ↦ hω.1)) hγ]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  change γ t * (∫ ω, U ω * f t ω ∂μ) = t * γ t
  rw [h.terminal_past_product hUm hU (hm t ht),mul_comm]

lemma bounded_multiplier_integral_difference {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U X Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    |(∫ ω, U ω*X ω ∂μ)-(∫ ω, U ω*Y ω ∂μ)|≤∫ ω, |X ω-Y ω| ∂μ := by
  have hUb : ∀ᵐ ω ∂μ, ‖U ω‖≤1 := hb.mono (fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω)
  have hUX := hX.bdd_mul hU hUb
  have hUY := hY.bdd_mul hU hUb
  rw [←integral_sub hUX hUY]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hUX.sub hUY).abs (hX.sub hY).abs
  filter_upwards [hb] with ω hω
  dsimp only [Pi.sub_apply]
  rw [←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_right hω (abs_nonneg _)).trans_eq (one_mul _)

lemma bounded_multiplier_integral_tendsto {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter I} {U : Ω → ℝ} {X : I → Ω → ℝ} {Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : ∀ᶠ t in l, Integrable (X t) μ) (hY : Integrable Y μ)
    (hL1 : Tendsto (fun t ↦ ∫ ω, |X t ω-Y ω| ∂μ) l (𝓝 (0 : ℝ))) :
    Tendsto (fun t ↦ ∫ ω, U ω*X t ω ∂μ) l (𝓝 (∫ ω, U ω*Y ω ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hL1
  filter_upwards [hX] with t ht
  simpa only [Real.norm_eq_abs] using bounded_multiplier_integral_difference hU hb ht hY

end SKValue

end

end OAI

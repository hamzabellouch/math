import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-! Nonnegative decreasing remaining masses vanish almost surely when
their expectations tend to zero. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SLEExactGauge

theorem ae_tendsto_zero_of_antitone_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hanti : ∀ᵐ ω ∂P, Antitone (fun n => f n ω))
    (hmean : Tendsto (fun n => ∫⁻ ω, f n ω ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have hi : (∫⁻ ω, liminf (fun n => f n ω) atTop ∂P) = 0 := by
    apply le_zero_iff.mp
    exact (lintegral_liminf_le hf).trans_eq hmean.liminf_eq
  have hz := (lintegral_eq_zero_iff (Measurable.liminf hf)).mp hi
  filter_upwards [hanti,hz] with ω ha hz
  have ht := tendsto_atTop_iInf ha
  have he : (⨅ n, f n ω) = 0 := ht.liminf_eq.symm.trans hz
  rwa [he] at ht

end SLEExactGauge

end

end OAI

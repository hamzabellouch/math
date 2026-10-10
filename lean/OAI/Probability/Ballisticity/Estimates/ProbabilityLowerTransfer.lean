import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma probability_lower_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p q cost : ℕ → Ω → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hp : Tendsto (fun i => μ.real {x | p i x < c}) atTop (𝓝 0))
    (hcost : TendstoInMeasure μ cost atTop (fun _ => 0))
    (hb : ∀ i, ∀ᵐ x ∂μ, |p i x-q i x| ≤ cost i x) :
    Tendsto (fun i => μ.real {x | q i x < c/2}) atTop (𝓝 0) := by
  have hh := (tendstoInMeasure_iff_measureReal_norm.mp hcost) (c/2) (half_pos hc)
  simp only [sub_zero] at hh
  have hlim : Tendsto (fun i => μ.real {x | p i x < c}+μ.real {x | c/2 ≤ ‖cost i x‖}) atTop (𝓝 0) := by
    simpa only [add_zero] using hp.add hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => measureReal_nonneg)
  intro i
  apply le_trans _ (measureReal_union_le {x | p i x < c} {x | c/2 ≤ ‖cost i x‖})
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hb i] with x hx
  intro hqx
  change q i x < c/2 at hqx
  change p i x < c ∨ c/2 ≤ ‖cost i x‖
  by_cases hpx : p i x < c
  · exact Or.inl hpx
  · right
    have hp' : c ≤ p i x := le_of_not_gt hpx
    have h' : p i x-q i x ≤ cost i x := (le_abs_self _).trans hx
    have h'' : cost i x ≤ ‖cost i x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (cost i x)
    linarith

end DirectionalTransience

end

end

end OAI

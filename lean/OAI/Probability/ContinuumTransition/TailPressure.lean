import OAI.Probability.ContinuumTransition.TailBounds

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem physical_pressure_tail_bound {t β : ℝ} (ht : 1 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) (h : ℝ) :
    0 ≤ physicalPressure (physicalProfile t (fun n => σ n+τ n) R) t (β,h)-
      physicalPressure (physicalProfile t σ R) t (β,h) ∧
    physicalPressure (physicalProfile t (fun n => σ n+τ n) R) t (β,h)-
      physicalPressure (physicalProfile t σ R) t (β,h) ≤
      108*2197*β*kernelHeight*momentConstant t β (t*h)*(∑' n, τ n) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hbfull : 2197*t*kernelHeight*(∑' n, (σ n+τ n))/2 ≤ t^2/8 := by
    nlinarith only [hsmall, sq_nonneg t]
  have hbσ := physical_small_subpart ht0.le hτ hs hτs hsmall
  have hlimσ := physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht hβ.le
    (physicalProfile_stable ht0.le hσ hR hs hbσ)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r) (h := h)
  have hlimfull := physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hστ hR (hs.add hτs))) ht hβ.le
    (physicalProfile_stable ht0.le hστ hR (hs.add hτs) hbfull)
    (fun r _ => physicalProfile_le_core ht0.le hστ hR r) (h := h)
  have hlim := hlimfull.sub hlimσ
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hh := (physical_log_tail_bound ht0 hβ hσ hτ hR hs hτs hsmall h L).1
    simpa only [← sub_div] using div_nonneg hh (mul_pos ht0 (pow_pos hL 3)).le
  · apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hh := (physical_log_tail_bound ht0 hβ hσ hτ hR hs hτs hsmall h L).2
    have hcard := cubeCells_card_coarse hL
    have hmc := momentConstant_pos ht0 hβ (t*h)
    have hmass : 0 ≤ ∑' n, τ n := tsum_nonneg hτ
    have hk := kernelHeight_pos
    have hc0 : 0 ≤ β*(momentConstant t β (t*h)/2)*(2197*t*kernelHeight*(∑' n, τ n)) := by
      positivity
    have hcard' := mul_le_mul_of_nonneg_left hcard hc0
    have hb : Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
        Real.log (grandPartition (physicalProfile t σ R) t β h L) ≤
        (108*2197*β*kernelHeight*momentConstant t β (t*h)*(∑' n, τ n))*(t*L^3) := by
      nlinarith only [hh, hcard']
    rw [← sub_div]
    exact (div_le_iff₀ (mul_pos ht0 (pow_pos hL0 3))).2 hb

end ContinuumTemperature
end

end OAI

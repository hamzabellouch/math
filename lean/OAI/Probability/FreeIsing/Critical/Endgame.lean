import OAI.Probability.FreeIsing.Critical.Reduction
import OAI.Probability.FreeIsing.Critical.TimeUniqueness
import OAI.Probability.FreeIsing.Estimates.LogInterpolation

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

structure CriticalEndpointBounds (D Q L Z S V C A B c K t : ℝ) : Prop where
  noise_nonneg : 0 ≤ S
  noise_le : S ≤ C * V
  small_loss : S ≤ A * t ^ ((1 : ℝ) / 4) * V +
    min (A * V) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))
  quadratic : Q ≤ C * (S * (1 / t + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2)
  linear : L ≤ C * (V * (t ^ (-(3 : ℝ) / 4) + Real.log (1 + Real.log (K / V))) + V ^ 2)
  square_root : Z ≤ C * (Real.sqrt S * (t ^ (-(3 : ℝ) / 4) +
    (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V)
  drift : D ≤ C * (V + Q + L + Real.sqrt V * Z)

def criticalEndgameConstant (C H A B c late : ℝ) : ℝ :=
  max (C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1)) late

theorem CriticalEndpointBounds.differential_bound
    {D Q L Z S V C H A B c K t : ℝ}
    (h : CriticalEndpointBounds D Q L Z S V C A B c K t)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hK : 1 ≤ K) (hV : 0 < V) (hVK : V ≤ K)
    (hVH : V ≤ H) (ht : 0 < t) (ht1 : t < 1) :
    D ≤ (C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1)) *
      V * (1 + Real.log (K / V)) *
      (1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hJ : 0 < (Real.log (1 / t)) ^ 2 :=
    sq_pos_of_pos (Real.log_pos ((one_lt_div ht).2 ht1))
  exact critical_differential_bound_of_endpoint_sums hC hH hI
    (by positivity) h.noise_nonneg hV.le hVH h.noise_le hJ ht
    (small_time_log_loss_of_minimum hA hB hc hK hV hVK ht ht1 h.small_loss)
    h.quadratic h.linear h.square_root h.drift

theorem eq_zero_of_ae_critical_endpoint_bounds
    {V Q L Z S : ℝ → ℝ} {T cutoff C H A B c K late : ℝ}
    (hT : 0 ≤ T) (hcutoff : cutoff < 1)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hK : 1 ≤ K)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupperK : ∀ t ∈ Icc 0 T, V t ≤ K)
    (hupperH : ∀ t ∈ Icc 0 T, V t ≤ H)
    (hendpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      CriticalEndpointBounds (deriv V t) (Q t) (L t) (Z t) (S t) (V t) C A B c K t)
    (hlate : ∀ᵐ t ∂volume.restrict (Ioc 0 T), cutoff < t → 0 < V t →
      deriv V t ≤ late * V t) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  let M := criticalEndgameConstant C H A B c late
  have hbase : 0 ≤ C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1) := by
    positivity
  have hM : 0 ≤ M := hbase.trans (le_max_left _ _)
  apply eq_zero_of_ae_small_critical_large_linear hT hcutoff hM hV hzero
    hnonneg hupperK (lt_of_lt_of_le zero_lt_one hK)
  · filter_upwards [hendpoint, ae_restrict_mem measurableSet_Ioc] with t he ht
    intro htc hpos
    have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have htpos : 0 < t := ht.1
    have hb := (he htc hpos).differential_bound hC hH hA hB hc hK hpos
      (hupperK t hmem) (hupperH t hmem) ht.1 (htc.trans_lt hcutoff)
    have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((one_le_div hpos).2 (hupperK t hmem))
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le
  · filter_upwards [hlate] with t hl
    intro ht hpos
    exact (hl ht hpos).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)

end Problem367

end

end OAI

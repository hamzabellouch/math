import OAI.Probability.FreeIsing.Critical.Endgame
import OAI.Probability.FreeIsing.Estimates.EndpointTimeScale

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

theorem eq_zero_of_ae_small_critical_large_osgood
    {V : ℝ → ℝ} {T K cutoff C : ℝ}
    (hT : 0 ≤ T) (hc : cutoff < 1)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc 0 T, V t ≤ K) (hK : 0 < K)
    (hsmall : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      deriv V t ≤ C * V t * (1 + Real.log (K / V t)) *
        (1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)))
    (hlarge : ∀ᵐ t ∂volume.restrict (Ioc 0 T), cutoff < t → 0 < V t →
      deriv V t ≤ C * V t * (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  apply eq_zero_of_ae_criticalTimeCoefficient hT hc hV hzero hnonneg hupper hK
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hsmall, hlarge] with t hs hl
  intro hpos
  by_cases ht : t ≤ cutoff
  · simpa only [criticalTimeCoefficient, ite_eq_left ht, mul_assoc, mul_left_comm,
      mul_comm] using hs ht hpos
  · simpa only [criticalTimeCoefficient, ite_eq_right ht, mul_one] using
      hl (lt_of_not_ge ht) hpos

theorem endpoint_sums_bounded_scale_reduction
    {D Q L Z S V C H I R W Rmax Wmax : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H)
    (hSV : S ≤ C * V) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hRmax : R ≤ Rmax) (hWmax : W ≤ Wmax)
    (hQ : Q ≤ C * (S * (R + (Real.log I) ^ 2) + V ^ 2))
    (hL : L ≤ C * (V * (W + Real.log I) + V ^ 2))
    (hZ : Z ≤ C * (Real.sqrt S * (W + (Real.log I) ^ ((3 : ℝ) / 2)) + V))
    (hD : D ≤ C * (V + Q + L + Real.sqrt V * Z)) :
    D ≤ (C ^ 2 * (9 * C + 3 * H + 3) * (C * Rmax + 1 + Wmax)) * V * I := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hRmax0 : 0 ≤ Rmax := hR.trans hRmax
  have hWmax0 : 0 ≤ Wmax := hW.trans hWmax
  have hVI : V ≤ V * I := by nlinarith
  have hnoise : S * R ≤ (C * Rmax) * (V * I) := by
    calc
      S * R ≤ (C * V) * Rmax := mul_le_mul hSV hRmax hR (by positivity)
      _ = (C * Rmax) * V := by ring
      _ ≤ (C * Rmax) * (V * I) :=
        mul_le_mul_of_nonneg_left hVI (by positivity)
  have hlinear : V * (I + W) ≤ (1 + Wmax) * (V * I) := by
    calc
      V * (I + W) ≤ V * I + Wmax * V := by
        nlinarith [mul_le_mul_of_nonneg_left hWmax hV]
      _ ≤ V * I + Wmax * (V * I) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hVI hWmax0)
      _ = (1 + Wmax) * (V * I) := by ring
  have hscale := endpoint_sums_critical_reduction hC hH hI hS hV hVH hSV
    hR hW hQ hL hZ hD
  calc
    D ≤ C ^ 2 * (9 * C + 3 * H + 3) * (S * R + V * (I + W)) := hscale
    _ ≤ C ^ 2 * (9 * C + 3 * H + 3) *
        ((C * Rmax) * (V * I) + (1 + Wmax) * (V * I)) :=
      mul_le_mul_of_nonneg_left (add_le_add hnoise hlinear) (by positivity)
    _ = _ := by ring

structure CriticalSpatialEndpointBounds (D Q L Z S V C K ω : ℝ) : Prop where
  noise_nonneg : 0 ≤ S
  noise_le : S ≤ C * V
  quadratic : Q ≤ C * (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2)
  linear : L ≤ C * (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2)
  square_root : Z ≤ C * (Real.sqrt S * (ω⁻¹ * Real.sqrt (ω⁻¹) +
    (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V)
  drift : D ≤ C * (V + Q + L + Real.sqrt V * Z)

theorem inv_le_inv_mul_sqrt {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ω⁻¹ ≤ ω⁻¹ * Real.sqrt (ω⁻¹) := by
  have hi : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).2 hω1
  have hs : 1 ≤ Real.sqrt (ω⁻¹) := by
    exact (Real.one_le_sqrt).2 hi
  simpa using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hω.le)

theorem CriticalSpatialEndpointBounds.small_time
    {D Q L Z S V C A B c K t : ℝ}
    (h : CriticalSpatialEndpointBounds D Q L Z S V C K (Real.sqrt t))
    (hC : 0 ≤ C) (hV : 0 ≤ V) (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : S ≤ A * t ^ ((1 : ℝ) / 4) * V +
      min (A * V) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    CriticalEndpointBounds D Q L Z S V C A B c K t := by
  refine ⟨h.noise_nonneg, h.noise_le, hsmall, ?_, ?_, ?_, h.drift⟩
  · simpa only [inv_sqrt_sq_time ht.le] using h.quadratic
  · apply h.linear.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hV
    exact add_le_add (inv_sqrt_le_time_three_quarters ht ht1) le_rfl
  · simpa only [inv_sqrt_mul_sqrt_time ht] using h.square_root

def criticalLateCoefficient (C H ε : ℝ) : ℝ :=
  C ^ 2 * (9 * C + 3 * H + 3) *
    (C * (ε⁻¹) ^ 2 + 1 + ε⁻¹ * Real.sqrt (ε⁻¹))

theorem CriticalSpatialEndpointBounds.late_time
    {D Q L Z S V C H K ω ε : ℝ}
    (h : CriticalSpatialEndpointBounds D Q L Z S V C K ω)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hV : 0 < V) (hVK : V ≤ K) (hVH : V ≤ H)
    (hε : 0 < ε) (hεω : ε ≤ ω) (hω1 : ω ≤ 1) :
    D ≤ criticalLateCoefficient C H ε * V * (1 + Real.log (K / V)) := by
  have hω : 0 < ω := hε.trans_le hεω
  have hωinv : 0 ≤ ω⁻¹ := inv_nonneg.mpr hω.le
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have hinv : ω⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hω hε).2 hεω
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have := Real.log_nonneg ((one_le_div hV).2 hVK)
    linarith
  have hlinear : L ≤ C * (V *
      (ω⁻¹ * Real.sqrt (ω⁻¹) + Real.log (1 + Real.log (K / V))) + V ^ 2) := by
    apply h.linear.trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hV.le
    exact add_le_add (inv_le_inv_mul_sqrt hω hω1) le_rfl
  exact endpoint_sums_bounded_scale_reduction hC hH hI h.noise_nonneg hV.le hVH
    h.noise_le (sq_nonneg _) (mul_nonneg hωinv (Real.sqrt_nonneg _))
    ((sq_le_sq₀ hωinv hεinv).2 hinv)
    (mul_le_mul hinv (Real.sqrt_le_sqrt hinv) (Real.sqrt_nonneg _) hεinv)
    h.quadratic hlinear h.square_root h.drift

theorem eq_zero_of_ae_critical_spatial_endpoint_bounds
    {V Q L Z S : ℝ → ℝ} {T cutoff C H A B c K : ℝ}
    (hT : 0 ≤ T) (hcutoff0 : 0 < cutoff) (hcutoff : cutoff < 1)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hK : 1 ≤ K)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupperK : ∀ t ∈ Icc 0 T, V t ≤ K)
    (hupperH : ∀ t ∈ Icc 0 T, V t ≤ H)
    (hendpoint : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 < V t →
      CriticalSpatialEndpointBounds (deriv V t) (Q t) (L t) (Z t) (S t) (V t) C K
        (min (Real.sqrt t) 1))
    (hsmall : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      S t ≤ A * t ^ ((1 : ℝ) / 4) * V t +
        min (A * V t) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  let early := C ^ 2 * (9 * C + 3 * H + 3) * (A + 2 * (A + B) / c + 1)
  let late := criticalLateCoefficient C H (Real.sqrt cutoff)
  let M := max early late
  apply eq_zero_of_ae_small_critical_large_osgood (C := M) hT hcutoff hV hzero
    hnonneg hupperK (zero_lt_one.trans_le hK)
  · filter_upwards [hendpoint, hsmall, ae_restrict_mem measurableSet_Ioc] with t he hs ht
    intro htc hpos
    have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have ht1 : t < 1 := htc.trans_lt hcutoff
    have htpos : 0 < t := ht.1
    have hscale : min (Real.sqrt t) 1 = Real.sqrt t :=
      min_eq_left (Real.sqrt_le_one.2 ht1.le)
    have he' := he hpos
    rw [hscale] at he'
    have hb := (he'.small_time (zero_le_one.trans hC) hpos.le ht.1 ht1.le
      (hs htc hpos)).differential_bound hC hH hA hB hc hK hpos
        (hupperK t hmem) (hupperH t hmem) ht.1 ht1
    have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((one_le_div hpos).2 (hupperK t hmem))
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left early late) hpos.le
  · filter_upwards [hendpoint, ae_restrict_mem measurableSet_Ioc] with t he ht
    intro htc hpos
    have hmem : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hscale : Real.sqrt cutoff ≤ min (Real.sqrt t) 1 :=
      le_min (Real.sqrt_le_sqrt htc.le) (Real.sqrt_le_one.2 hcutoff.le)
    have hb := (he hpos).late_time hC hH hpos (hupperK t hmem) (hupperH t hmem)
      (Real.sqrt_pos.2 hcutoff0) hscale (min_le_right _ _)
    have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((one_le_div hpos).2 (hupperK t hmem))
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_right early late) hpos.le

end Problem367

end

end OAI

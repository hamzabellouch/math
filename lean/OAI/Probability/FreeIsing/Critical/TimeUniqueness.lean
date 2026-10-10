import OAI.Probability.FreeIsing.Critical.Comparison

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

theorem eq_zero_of_ae_criticalTimeCoefficient {V : ℝ → ℝ} {T K cutoff C : ℝ}
    (hT : 0 ≤ T) (hc : cutoff < 1)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc 0 T, V t ≤ K) (hK : 0 < K)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 < V t →
      deriv V t ≤ criticalTimeCoefficient cutoff C t * V t *
        (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  exact eq_zero_of_ae_osgood hV hzero hnonneg hupper hK
    (criticalTimeCoefficient_intervalIntegrable C hT hc) hbound

theorem eq_zero_of_ae_small_critical_large_linear
    {V : ℝ → ℝ} {T K cutoff C : ℝ}
    (hT : 0 ≤ T) (hc : cutoff < 1) (hC : 0 ≤ C)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc 0 T, V t ≤ K) (hK : 0 < K)
    (hsmall : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ≤ cutoff → 0 < V t →
      deriv V t ≤ C * V t * (1 + Real.log (K / V t)) *
        (1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)))
    (hlarge : ∀ᵐ t ∂volume.restrict (Ioc 0 T), cutoff < t → 0 < V t →
      deriv V t ≤ C * V t) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  apply eq_zero_of_ae_criticalTimeCoefficient hT hc hV hzero hnonneg hupper hK
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hsmall, hlarge, ae_restrict_mem measurableSet_Ioc] with t hs hl ht
  intro hpos
  by_cases htc : t ≤ cutoff
  · simpa only [criticalTimeCoefficient, ite_eq_left htc, mul_assoc, mul_left_comm,
      mul_comm] using hs htc hpos
  · have hlog : 0 ≤ Real.log (K / V t) :=
      Real.log_nonneg ((le_div_iff₀ hpos).2 (by
        simpa using hupper t ⟨ht.1.le, ht.2⟩))
    have hmul : C * V t ≤ C * V t * (1 + Real.log (K / V t)) := by
      nlinarith [mul_nonneg (mul_nonneg hC hpos.le) hlog]
    simpa only [criticalTimeCoefficient, ite_eq_right htc, mul_one] using
      (hl (lt_of_not_ge htc) hpos).trans hmul

end Problem367

end

end OAI

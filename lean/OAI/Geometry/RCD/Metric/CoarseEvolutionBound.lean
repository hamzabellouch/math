import OAI.Geometry.RCD.Metric.EvolutionInitialLimit

namespace OAI

/-! # A short-time sufficient form of the dimensional evolution bound

Bounding the exponential integral by its endpoint retains the sharp
coefficient at time zero, as required for the integrated Bochner limit.
-/

namespace RegularPointCoordinates

theorem gronwallBound_one_le {d k e : ℝ} (hk : 0 ≤ k) (he : 0 ≤ e) :
    gronwallBound d k e 1 ≤ (d+e)*Real.exp k := by
  by_cases hk0 : k=0
  · simp only [hk0,gronwallBound_K0,mul_one,Real.exp_zero,le_refl]
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have h := Real.add_one_le_exp (-k)
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos k).le
    rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero k)] at hh
    have hr : (Real.exp k-1)/k ≤ Real.exp k := by
      apply (div_le_iff₀ hkp).mpr
      nlinarith only [hh]
    have hr' := mul_le_mul_of_nonneg_left hr he
    simp only [gronwallBound_of_K_ne_0 hk0,mul_one]
    calc d*Real.exp k+e/k*(Real.exp k-1)
        = d*Real.exp k+e*((Real.exp k-1)/k) := by ring
      _ ≤ d*Real.exp k+e*Real.exp k := add_le_add le_rfl hr'
      _ = (d+e)*Real.exp k := by ring

end RegularPointCoordinates

end OAI

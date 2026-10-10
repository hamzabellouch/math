import OAI.Probability.SLE.Loewner.CapacityRadiusBound

namespace OAI

/-! The capacity of initial subarcs tends to zero at the starting point,
by the explicit half-disk capacity bound. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

theorem initialCapacity_continuousAt_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ContinuousAt (initialCapacity p hi h0 hH) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let R : ℝ := Real.sqrt ε/2
  have hR : 0<R := div_pos (Real.sqrt_pos.mpr hε) (by norm_num)
  have hR2 : R^2<ε := by
    dsimp only [R]
    nlinarith [Real.sq_sqrt hε.le,Real.sqrt_nonneg ε]
  have hp := p.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds (p 0) hR)
  obtain ⟨δ,hδ,hδp⟩ := Metric.mem_nhds_iff.mp hp
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have hbound : ∀ u ∈ Icc (0:unitInterval) t, ‖p u‖≤R := by
    intro u hu
    have hdist : dist u (0:unitInterval) ≤ dist t (0:unitInterval) := by
      change |(u:ℝ)-0|≤|(t:ℝ)-0|
      simp only [sub_zero,abs_of_nonneg u.property.1,abs_of_nonneg t.property.1]
      exact_mod_cast hu.2
    have hpu := hδp (hdist.trans_lt ht)
    have hlt : ‖p u‖<R := by
      simpa only [mem_preimage,mem_ball,h0,dist_zero_right] using hpu
    exact hlt.le
  have hc := initialCapacity_le_radius_sq p hi h0 hH hR t hbound
  rw [initialCapacity_zero,Real.dist_eq,sub_zero,
    abs_of_nonneg (initialCapacity_nonneg p hi h0 hH t)]
  exact hc.trans_lt hR2

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.RawLifetimeFlowLimit
import OAI.Probability.SLE.Geometry.OpenBoundaryTrace

namespace OAI

/-! A point lost by the smooth raw flow is exactly the trace tip at its
finite lifetime. The reverse path is the forward path read backwards. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem eq_trace_at_lifetime
    (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) {τ : ℝ} (hτ : 0 < τ)
    (hs : ∀ t, 0 ≤ t → t < τ → Surviving 1 b z t)
    (hdead : ¬Surviving 1 b z τ) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (driverValue b) (b' t) (Icc 0 τ) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 τ, |b' t| ≤ L) :
    z=trace 1 b τ := by
  let f := Function.update (flow 1 b z) τ (driverValue b τ : ℂ)
  let q (t : ℝ) := f (τ-t)
  have hqeq (t : ℝ) (ht : 0 < t) : q t=flow 1 b z (τ-t) := by
    exact Function.update_of_ne (by linarith : τ-t ≠ τ) _ _
  have hqc : ContinuousOn q (Icc 0 τ) := by
    apply (continuousOn_flow_with_terminal_driver b z hz hτ hs hdead).comp
      (continuous_const.sub continuous_id).continuousOn
    intro t ht
    exact ⟨sub_nonneg.mpr ht.2,sub_le_self _ ht.1⟩
  have hq0 : q 0=(b (⟨τ,hτ.le⟩ : ℝ≥0) : ℂ) := by
    simp only [q,f,sub_zero,Function.update_self]
    change (b τ.toNNReal : ℂ) = _
    have ht : τ.toNNReal = (⟨τ,hτ.le⟩ : ℝ≥0) := by
      apply Subtype.ext
      exact Real.coe_toNNReal τ hτ.le
    rw [ht]
  have hqp (t : ℝ) (ht : t ∈ Ioc 0 τ) : 0 < (q t).im := by
    rw [hqeq t ht.1]
    exact surviving_flow_mem_upperHalfPlane 1 b z (τ-t) (sub_nonneg.mpr ht.2)
      (hs _ (sub_nonneg.mpr ht.2) (by linarith [ht.1]))
  have hqd (t : ℝ) (ht : t ∈ Ioo 0 τ) : HasDerivWithinAt q
      (-2/(q t-(driverValue b (τ-t) : ℂ))) (Ici t) t := by
    have hx : 0 < τ-t := sub_pos.mpr ht.2
    let S : ℝ := ((τ-t)+τ)/2
    have hxS : τ-t < S := by dsimp [S]; linarith [ht.1]
    have hSτ : S < τ := by dsimp [S]; linarith [ht.1]
    have hflow := (flow_hasDerivWithinAt_of_later_survival 1 b z (τ-t) S hx.le hxS
      (hs S (hx.le.trans hxS.le) hSτ)).hasDerivAt (Ici_mem_nhds hx)
    have hh := hflow.scomp t ((hasDerivAt_id t).const_sub τ)
    have hevent : q =ᶠ[𝓝[Ici t] t] (fun s : ℝ => flow 1 b z (τ-s)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (lt_mem_nhds ht.1)] with s hs'
      exact hqeq s hs'
    have hh' := hh.hasDerivWithinAt.congr_of_eventuallyEq hevent (hqeq t ht.1)
    convert! hh' using 1
    rw [hqeq t ht.1]
    simp [a,neg_div]
  have hfinal : q τ=z := by
    rw [hqeq τ hτ,sub_self,flow_zero 1 b z hz]
  have htip := boundary_reverse_eq_trace_of_open_derivative b ⟨τ,hτ.le⟩ hτ b'
    hd hL hb q hqc hq0 hqd hqp
  exact hfinal.symm.trans htip

end SLEExactGauge.Target

end

end OAI

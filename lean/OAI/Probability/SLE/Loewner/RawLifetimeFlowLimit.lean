import OAI.Probability.SLE.Loewner.RawLifetimeHeightLimit
import OAI.Probability.SLE.Loewner.RawForwardCoordinates
import OAI.Probability.SLE.Loewner.VanishingHeightRealLimit

namespace OAI

/-! Both coordinates of the raw forward flow approach the driver at a
finite lifetime. Updating the terminal value gives a continuous path. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

theorem flow_tendsto_driver_at_lifetime
    (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) {τ : ℝ} (hτ : 0 < τ)
    (hs : ∀ t, 0 ≤ t → t < τ → Surviving 1 b z t)
    (hdead : ¬Surviving 1 b z τ) :
    Tendsto (flow 1 b z) (𝓝[<] τ) (𝓝 (driverValue b τ : ℂ)) := by
  have hc := flow_continuousOn_before_lifetime b z (fun t ht => hs t ht.1 ht.2)
  have hy := flow_height_tendsto_zero_at_lifetime b z hz hτ hs hdead
  have hd (t : ℝ) (ht : t ∈ Ico 0 τ) :=
    flow_coordinate_derivatives b z ht.1
      (show t < (t+τ)/2 by linarith [ht.2])
      (hs ((t+τ)/2) (by linarith [ht.1,ht.2]) (by linarith [ht.2]))
  have hx := forward_real_tendsto_driver_of_height_zero hτ
    (fun t => (flow 1 b z t).re) (fun t => (flow 1 b z t).im) (driverValue b)
    (Complex.continuous_re.comp_continuousOn hc)
    (Complex.continuous_im.comp_continuousOn hc)
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    (fun t ht => surviving_flow_mem_upperHalfPlane 1 b z t ht.1 (hs t ht.1 ht.2))
    (b.continuous.comp continuous_real_toNNReal).continuousAt hy
  have hh := hx.ofReal.add (hy.ofReal.mul_const I)
  simpa only [ofReal_zero,zero_mul,add_zero,re_add_im] using hh

theorem continuousOn_flow_with_terminal_driver
    (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) {τ : ℝ} (hτ : 0 < τ)
    (hs : ∀ t, 0 ≤ t → t < τ → Surviving 1 b z t)
    (hdead : ¬Surviving 1 b z τ) :
    ContinuousOn (Function.update (flow 1 b z) τ (driverValue b τ : ℂ)) (Icc 0 τ) := by
  have heq : Icc 0 τ \ {τ} = Ico 0 τ := by
    ext t
    simp only [Set.mem_sdiff,mem_Icc,mem_singleton_iff,mem_Ico]
    constructor
    · rintro ⟨⟨ht0,htτ⟩,hne⟩
      exact ⟨ht0,lt_of_le_of_ne htτ hne⟩
    · rintro ⟨ht0,htτ⟩
      exact ⟨⟨ht0,htτ.le⟩,htτ.ne⟩
  apply continuousOn_update_iff.mpr
  rw [heq]
  refine ⟨flow_continuousOn_before_lifetime b z (fun t ht => hs t ht.1 ht.2),?_⟩
  intro _
  exact (flow_tendsto_driver_at_lifetime b z hz hτ hs hdead).mono_left
    (nhdsWithin_mono _ Ico_subset_Iio_self)

end SLEExactGauge.Target

end

end OAI

import OAI.Probability.SLE.Loewner.ForwardCapacityError
import OAI.Probability.SLE.Loewner.RawForwardHeight

namespace OAI

/-! Hydrodynamic normalization of the raw forward map follows from its
ODE on surviving trajectories, without a prior geometric witness. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem flow_hydrodynamic_normalization (b : Driver) (T : ℝ≥0) :
    Tendsto (fun z : ℂ => z*(flow 1 b z T-z))
      (cocompact ℂ ⊓ 𝓟 {z | Surviving 1 b z T}) (𝓝 (2*(T : ℂ))) := by
  have hc : Continuous (driverValue b) := b.continuous.comp continuous_real_toNNReal
  obtain ⟨M,hM,hMb⟩ := (isCompact_Icc.image hc).isBounded.exists_pos_norm_lt
  have hbound (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : |driverValue b t| ≤ M := by
    simpa only [Real.norm_eq_abs] using (hMb _ (mem_image_of_mem _ ht)).le
  have hfar (z : ℂ) (hz : Surviving 1 b z T)
      (hlarge : 8*(M+(T : ℝ)+1) ≤ ‖z‖) :
      ‖z*(flow 1 b z T-z)-2*(T : ℂ)‖ ≤ 4*(T : ℝ)*(M+T)/‖z‖ := by
    have hzH := surviving_mem_upperHalfPlane 1 b z T T.coe_nonneg hz
    apply forward_far_capacity_error T.coe_nonneg hM.le
      (flow 1 b z) (driverValue b) z
      (flow_continuousOn_of_survival 1 b z T.coe_nonneg hz) (flow_zero 1 b z hzH)
      (fun t ht => ?_) hbound hlarge
    let S : ℝ := (t+T)/2
    have htS : t < S := by dsimp [S]; linarith [ht.2]
    have hST : S ≤ T := by dsimp [S]; linarith [ht.2]
    have hS : 0 ≤ S := ht.1.trans htS.le
    have hh := (flow_hasDerivWithinAt_of_later_survival 1 b z t S ht.1 htS
      (surviving_of_le_time 1 b z hS hST hz)).mono (Ici_subset_Ici.mpr ht.1)
    simpa only [a,div_one,ofReal_ofNat] using hh
  let l := cocompact ℂ ⊓ 𝓟 {z | Surviving 1 b z T}
  have herr : Tendsto (fun z : ℂ => z*(flow 1 b z T-z)-2*(T : ℂ)) l (𝓝 0) := by
    apply squeeze_zero_norm'
    · change ∀ᶠ z in cocompact ℂ ⊓ 𝓟 {z | Surviving 1 b z T},
        ‖z*(flow 1 b z T-z)-2*(T : ℂ)‖ ≤ 4*(T : ℝ)*(M+T)/‖z‖
      rw [eventually_inf_principal]
      filter_upwards [tendsto_norm_cocompact_atTop.eventually
        (eventually_ge_atTop (8*(M+(T : ℝ)+1)))] with z hz
      exact fun hsurvive => hfar z hsurvive hz
    · exact tendsto_const_nhds.div_atTop
        (tendsto_norm_cocompact_atTop.mono_left inf_le_left)
  simpa only [sub_add_cancel,zero_add] using herr.add_const (2*(T : ℂ))

end SLEExactGauge.Target

end

end OAI

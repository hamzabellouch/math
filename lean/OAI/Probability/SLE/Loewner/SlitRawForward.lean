import OAI.Probability.SLE.Loewner.SlitInitialEvolution
import OAI.Probability.SLE.Angle.TargetPositiveFlow

namespace OAI

/-! The raw positive Loewner trajectory agrees exactly with the
constructed conformal slit evolution on every surviving prefix. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem slitCapacityForward_eq_raw (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p (slitCapacityTime p hi h0 hH T t))) :
    Target.Surviving 1 (slitCapacityDriver p hi h0 hH hT) z t ∧
      Target.flow 1 (slitCapacityDriver p hi h0 hH hT) z t=
        slitCapacityForward p hi h0 hH T t z := by
  let Y := fun u : ℝ => slitCapacityForward p hi h0 hH T u.toNNReal z
  have hd := fun u (hu : u∈Icc 0 (t:ℝ)) =>
    slitCapacityForward_derivative_upto p hi h0 hH hT ht hz hu
  have hc : ContinuousOn Y (Icc 0 (t:ℝ)) := fun u hu => (hd u hu).continuousWithinAt
  have hpos (u : ℝ) (hu : u∈Icc 0 (t:ℝ)) : 0<(Y u).im := by
    have hu' : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hu.2
    have hclock : slitCapacityTime p hi h0 hH T u.toNNReal ≤ slitCapacityTime p hi h0 hH T t := by
      apply (initialCapacity_strictMono p hi h0 hH).le_iff_le.mp
      rw [slitCapacityTime_capacity p hi h0 hH T (hu'.trans ht),
        slitCapacityTime_capacity p hi h0 hH T ht,Real.coe_toNNReal u hu.1]
      linarith [hu.2]
    exact initialForwardChart_im_pos p hi h0 hH _
      ⟨hz.1,fun he => hz.2 (initialSubarc_range_mono p hclock he)⟩
  obtain ⟨v,hv,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr t.coe_nonneg)
    (Complex.continuous_im.comp_continuousOn hc)
  have hY0 : Y 0=z := by
    simp only [Y,Real.toNNReal_zero,slitCapacityForward,slitCapacityTime_zero,
      initialForwardChart_zero,id_eq]
  have hh := Target.flow_eq_of_positive_trajectory 1 (slitCapacityDriver p hi h0 hH hT) z t
    t.coe_nonneg Y hc hY0 (Y v).im (hpos v hv) (fun u hu => hmin hu) (fun u hu => ?_)
  · simpa only [Y,Real.toNNReal_coe] using hh
  · have he := hasDerivWithinAt_Ici_of_Icc hu (hd u (Ico_subset_Icc_self hu))
    simpa only [Target.a,div_one,ofReal_ofNat,Target.driverValue,Y] using he

end SLEExactGauge

end

end OAI

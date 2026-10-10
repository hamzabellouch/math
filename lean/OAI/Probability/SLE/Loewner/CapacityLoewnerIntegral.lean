import OAI.Probability.SLE.Loewner.CapacityDriverContinuity
import OAI.Probability.SLE.Loewner.CapacityPointwiseLoewner

namespace OAI

/-! The right Loewner evolution has a continuous kernel. Its integral
identity therefore gives the ordinary derivative on the full prefix. -/
noncomputable section
open Set Filter Function Complex MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem capacityForward_integral_kernel (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    {c : ℝ} (hc : c∈Icc 0 (initialCapacity p hi h0 hH T)) :
    (∫ u in 0..c, 1/(capacityForwardOnPrefix p hi h0 hH T z u-
      (capacityDriverOnPrefix p hi h0 hH T hT u:ℂ)))=
      capacityForwardOnPrefix p hi h0 hH T z c-capacityForwardOnPrefix p hi h0 hH T z 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hc.1
    (capacityForwardOnPrefix_lipschitz p hi h0 hH hT hz).continuous.continuousOn
  · intro u hu
    exact (capacityForward_hasDerivWithinAt_Ici p hi h0 hH hT hz
      ⟨hu.1.le,hu.2.trans_le hc.2⟩).mono Ioi_subset_Ici_self
  · exact (capacityLoewnerKernel_continuous p hi h0 hH hT hz).intervalIntegrable 0 c

theorem capacityForward_hasDerivWithinAt_prefix (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    {c : ℝ} (hc : c∈Icc 0 (initialCapacity p hi h0 hH T)) :
    HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
      (1/(capacityForwardOnPrefix p hi h0 hH T z c-
        (capacityDriverOnPrefix p hi h0 hH T hT c:ℂ)))
      (Icc 0 (initialCapacity p hi h0 hH T)) c := by
  let f := capacityForwardOnPrefix p hi h0 hH T z
  let k := fun u => 1/(f u-(capacityDriverOnPrefix p hi h0 hH T hT u:ℂ))
  have hk : Continuous k := capacityLoewnerKernel_continuous p hi h0 hH hT hz
  have hI : HasDerivAt (fun u => f 0+∫ v in 0..u, k v) (k c) c := by
    simpa only [zero_add] using (intervalIntegral.integral_hasDerivAt_right
      (hk.intervalIntegrable 0 c) hk.aestronglyMeasurable.stronglyMeasurableAtFilter
        hk.continuousAt).const_add (f 0)
  apply hI.hasDerivWithinAt.congr_of_mem (fun u hu => ?_) hc
  change f u=f 0+∫ v in 0..u, k v
  rw [capacityForward_integral_kernel p hi h0 hH hT hz hu]
  dsimp only [f]
  abel

end SLEExactGauge

end

end OAI

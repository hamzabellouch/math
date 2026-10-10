import OAI.Probability.SLE.Loewner.CapacityLoewnerDerivative

namespace OAI

/-! Pointwise right evolution on every finite surviving capacity prefix. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem capacityForward_hasDerivWithinAt_Ici (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    {c : ℝ} (hc : c∈Ico 0 (initialCapacity p hi h0 hH T)) :
    HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
      (1/(capacityForwardOnPrefix p hi h0 hH T z c-
        (capacityDriverOnPrefix p hi h0 hH T hT c:ℂ))) (Ici c) c := by
  let s := capacityParameterOnPrefix p hi h0 hH T c
  have hcap : initialCapacity p hi h0 hH s=c :=
    capacityParameterOnPrefix_capacity p hi h0 hH T ⟨hc.1,hc.2.le⟩
  have hsT : s<T := (initialCapacity_strictMono p hi h0 hH).lt_iff_lt.mp
    (by rw [hcap]; exact hc.2)
  have hcaplt := initialCapacity_strictMono p hi h0 hH hsT
  have hr : HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
      (1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hsT.trans hT):ℂ)))
      (Ioi (initialCapacity p hi h0 hH s)) (initialCapacity p hi h0 hH s) := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (capacityForward_hasDerivWithinAt_right p hi h0 hH hsT hT hz)
    rwa [nhdsWithin_Ioc_eq_nhdsGT hcaplt] at hh
  have hh := hr.Ici_of_Ioi
  rw [← capacityForwardOnPrefix_at_initialCapacity p hi h0 hH T z hsT.le,hcap] at hh
  exact hh

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.SlitRawTrace

namespace OAI

/-! The constructed driver is constant after the chosen finite slit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma slitCapacityTime_after (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : slitCapacityHorizon p hi h0 hH T ≤ t) :
    slitCapacityTime p hi h0 hH T t=T := by
  have hright : initialCapacity p hi h0 hH T ≤ 2*(t:ℝ) := by
    change initialCapacity p hi h0 hH T/2 ≤ (t:ℝ) at ht
    linarith
  unfold slitCapacityTime capacityParameterOnPrefix
  rw [projIcc_of_right_le _ hright]
  apply (initialCapacity_strictMono p hi h0 hH).injective
  exact prefixCapacityTime_capacity p hi h0 hH T _

lemma slitCapacityDriver_after (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : slitCapacityHorizon p hi h0 hH T ≤ t) :
    slitCapacityDriver p hi h0 hH hT t=initialDrivingValue p hi h0 hH T hT := by
  change initialDrivingValue p hi h0 hH (slitCapacityTime p hi h0 hH T t)
    ((slitCapacityTime_le p hi h0 hH T t).trans_lt hT)=_
  congr 1
  exact slitCapacityTime_after p hi h0 hH T ht

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.SlitPhysicalEvolution

namespace OAI

/-! Exact agreement of the capacity-two clocks on nested prefixes. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma slitCapacityHorizon_mono (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {S T : unitInterval} (hST : S ≤ T) :
    slitCapacityHorizon p hi h0 hH S ≤ slitCapacityHorizon p hi h0 hH T := by
  change initialCapacity p hi h0 hH S/2 ≤ initialCapacity p hi h0 hH T/2
  exact div_le_div_of_nonneg_right (initialCapacity_monotone p hi h0 hH hST) (by norm_num)

lemma slitCapacityHorizon_time (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    slitCapacityHorizon p hi h0 hH (slitCapacityTime p hi h0 hH T t)=t := by
  apply NNReal.coe_injective
  change initialCapacity p hi h0 hH (slitCapacityTime p hi h0 hH T t)/2=(t:ℝ)
  rw [slitCapacityTime_capacity p hi h0 hH T ht]
  ring

lemma slitCapacityTime_restrict (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {S T : unitInterval} (hST : S ≤ T) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH S) :
    slitCapacityTime p hi h0 hH T t=slitCapacityTime p hi h0 hH S t := by
  apply (initialCapacity_strictMono p hi h0 hH).injective
  rw [slitCapacityTime_capacity p hi h0 hH T
    (ht.trans (slitCapacityHorizon_mono p hi h0 hH hST)),
    slitCapacityTime_capacity p hi h0 hH S ht]

lemma slitCapacityForward_restrict (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {S T : unitInterval} (hST : S ≤ T) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH S) :
    slitCapacityForward p hi h0 hH T t=slitCapacityForward p hi h0 hH S t := by
  unfold slitCapacityForward
  rw [slitCapacityTime_restrict p hi h0 hH hST ht]

lemma slitCapacityDriver_restrict (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {S T : unitInterval} (hST : S ≤ T) (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH S) :
    slitCapacityDriver p hi h0 hH hT t=
      slitCapacityDriver p hi h0 hH (hST.trans_lt hT) t := by
  change initialDrivingValue p hi h0 hH (slitCapacityTime p hi h0 hH T t)
    ((slitCapacityTime_le p hi h0 hH T t).trans_lt hT)=
    initialDrivingValue p hi h0 hH (slitCapacityTime p hi h0 hH S t)
      ((slitCapacityTime_le p hi h0 hH S t).trans_lt (hST.trans_lt hT))
  congr 1
  exact slitCapacityTime_restrict p hi h0 hH hST ht

end SLEExactGauge

end

end OAI

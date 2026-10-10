import OAI.Probability.SLE.Loewner.CapacityForwardDerivative

namespace OAI

/-! Continuity and exact values of the real, clipped capacity clock. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

noncomputable def capacityParameterOnPrefix (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (c : ℝ) : unitInterval :=
  prefixCapacityTime p hi h0 hH T
    (projIcc 0 (initialCapacity p hi h0 hH T) (initialCapacity_nonneg p hi h0 hH T) c)

lemma prefixCapacityTime_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : Continuous (prefixCapacityTime p hi h0 hH T) := by
  unfold prefixCapacityTime
  exact (initialCapacityHomeomorph p hi h0 hH).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)

lemma capacityParameterOnPrefix_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : Continuous (capacityParameterOnPrefix p hi h0 hH T) :=
  (prefixCapacityTime_continuous p hi h0 hH T).comp
    (LipschitzWith.projIcc (initialCapacity_nonneg p hi h0 hH T)).continuous

lemma capacityParameterOnPrefix_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {c : ℝ} (hc : c∈Icc 0 (initialCapacity p hi h0 hH T)) :
    initialCapacity p hi h0 hH (capacityParameterOnPrefix p hi h0 hH T c)=c := by
  rw [capacityParameterOnPrefix,prefixCapacityTime_capacity,projIcc_of_mem _ hc]

lemma capacityParameterOnPrefix_at_initialCapacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {s : unitInterval} (hs : s≤T) :
    capacityParameterOnPrefix p hi h0 hH T (initialCapacity p hi h0 hH s)=s := by
  apply (initialCapacity_strictMono p hi h0 hH).injective
  exact capacityParameterOnPrefix_capacity p hi h0 hH T
    ⟨initialCapacity_nonneg p hi h0 hH s,initialCapacity_monotone p hi h0 hH hs⟩

lemma capacityParameterOnPrefix_mem_Ioc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {s : unitInterval} {c : ℝ}
    (hc : c∈Ioc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH T)) :
    capacityParameterOnPrefix p hi h0 hH T c∈Ioc s T := by
  have hcap := capacityParameterOnPrefix_capacity p hi h0 hH T
    ⟨(initialCapacity_nonneg p hi h0 hH s).trans hc.1.le,hc.2⟩
  constructor
  · apply (initialCapacity_strictMono p hi h0 hH).lt_iff_lt.mp
    rw [hcap]
    exact hc.1
  · apply (initialCapacity_strictMono p hi h0 hH).le_iff_le.mp
    rw [hcap]
    exact hc.2

end SLEExactGauge

end

end OAI

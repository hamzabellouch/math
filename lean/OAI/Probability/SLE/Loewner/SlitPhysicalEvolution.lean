import OAI.Probability.SLE.Loewner.SlitPhysicalClock

namespace OAI

/-! Exact capacity-two forward and inverse maps on a finite physical prefix. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

noncomputable def slitCapacityForward (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (t : ℝ≥0) : ℂ → ℂ :=
  initialForwardChart p hi h0 hH (slitCapacityTime p hi h0 hH T t)

noncomputable def slitCapacityInverse (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (t : ℝ≥0) : ℂ → ℂ :=
  initialInverseChart p hi h0 hH (slitCapacityTime p hi h0 hH T t)

theorem slitCapacityForward_prefix_derivative (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T))
    {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    HasDerivWithinAt (fun u : ℝ => slitCapacityForward p hi h0 hH T u.toNNReal z)
      (2/(slitCapacityForward p hi h0 hH T t z-(slitCapacityDriver p hi h0 hH hT t:ℂ)))
      (Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) (t:ℝ) := by
  have ht' : 2*(t:ℝ)∈Icc 0 (initialCapacity p hi h0 hH T) := by
    constructor
    · positivity
    · change (t:ℝ) ≤ initialCapacity p hi h0 hH T/2 at ht
      linarith
  have hd := capacityForward_hasDerivWithinAt_prefix p hi h0 hH hT hz ht'
  have hmul : HasDerivWithinAt (fun u : ℝ => 2*u) 2
      (Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) (t:ℝ) := by
    simpa using ((hasDerivAt_id (t:ℝ)).const_mul 2).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => 2*u)
      (Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ))
      (Icc 0 (initialCapacity p hi h0 hH T)) := by
    intro u hu
    constructor
    · linarith [hu.1]
    · have hu2 : u ≤ initialCapacity p hi h0 hH T/2 := hu.2
      linarith
  have hh := hd.scomp (t:ℝ) hmul hmaps
  have he (u : ℝ) (hu : 0 ≤ u) :
      slitCapacityForward p hi h0 hH T u.toNNReal z=
        capacityForwardOnPrefix p hi h0 hH T z (2*u) := by
    simp only [slitCapacityForward,slitCapacityTime,Real.coe_toNNReal u hu,
      capacityForwardOnPrefix,capacityParameterOnPrefix]
  have hres := hh.congr (fun u hu => he u hu.1) (he t t.coe_nonneg)
  convert hres using 1
  change 2/(capacityForwardOnPrefix p hi h0 hH T z (2*(t:ℝ))-
    (capacityDriverOnPrefix p hi h0 hH T hT (2*(t:ℝ)):ℂ))=2 • _
  simp only [real_smul,Complex.ofReal_ofNat,mul_one_div]

end SLEExactGauge

end

end OAI

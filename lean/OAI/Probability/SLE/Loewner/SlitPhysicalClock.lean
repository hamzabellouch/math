import OAI.Probability.SLE.Loewner.InitialDrivingTip
import OAI.Probability.SLE.MomentGauge

namespace OAI

/-! The exact capacity-two parametrization of a finite prescribed slit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

noncomputable def slitCapacityHorizon (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : ℝ≥0 :=
  ⟨initialCapacity p hi h0 hH T/2,div_nonneg (initialCapacity_nonneg p hi h0 hH T) (by norm_num)⟩

noncomputable def slitCapacityTime (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (t : ℝ≥0) : unitInterval :=
  capacityParameterOnPrefix p hi h0 hH T (2*(t:ℝ))

lemma slitCapacityTime_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : Continuous (slitCapacityTime p hi h0 hH T) :=
  (capacityParameterOnPrefix_continuous p hi h0 hH T).comp
    (continuous_const.mul continuous_subtype_val)

@[simp] lemma slitCapacityTime_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : slitCapacityTime p hi h0 hH T 0=0 := by
  have hh := capacityParameterOnPrefix_at_initialCapacity p hi h0 hH T
    (s := 0) (show (0:unitInterval) ≤ T from T.property.1)
  simpa only [slitCapacityTime,NNReal.coe_zero,mul_zero,initialCapacity_zero] using hh

lemma slitCapacityTime_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (t : ℝ≥0) : slitCapacityTime p hi h0 hH T t ≤ T :=
  capacityParameterOnPrefix_le p hi h0 hH T _

lemma slitCapacityTime_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    initialCapacity p hi h0 hH (slitCapacityTime p hi h0 hH T t)=2*(t:ℝ) := by
  apply capacityParameterOnPrefix_capacity
  constructor
  · positivity
  · change (t:ℝ) ≤ initialCapacity p hi h0 hH T/2 at ht
    linarith

lemma slitCapacityTime_at_capacity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {v : unitInterval} (hv : v ≤ T) :
    slitCapacityTime p hi h0 hH T
      ⟨initialCapacity p hi h0 hH v/2,
        div_nonneg (initialCapacity_nonneg p hi h0 hH v) (by norm_num)⟩=v := by
  unfold slitCapacityTime
  change capacityParameterOnPrefix p hi h0 hH T (2*(initialCapacity p hi h0 hH v/2))=v
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
  exact capacityParameterOnPrefix_at_initialCapacity p hi h0 hH T hv

lemma slitCapacityTime_image (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    slitCapacityTime p hi h0 hH T '' Icc 0 t=Icc 0 (slitCapacityTime p hi h0 hH T t) := by
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨(slitCapacityTime p hi h0 hH T u).property.1,?_⟩
    apply (initialCapacity_strictMono p hi h0 hH).le_iff_le.mp
    rw [slitCapacityTime_capacity p hi h0 hH T (hu.2.trans ht),
      slitCapacityTime_capacity p hi h0 hH T ht]
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hu.2) (by norm_num)
  · intro hv
    let u : ℝ≥0 := ⟨initialCapacity p hi h0 hH v/2,
      div_nonneg (initialCapacity_nonneg p hi h0 hH v) (by norm_num)⟩
    refine ⟨u,⟨zero_le,?_⟩,slitCapacityTime_at_capacity p hi h0 hH T
      (hv.2.trans (slitCapacityTime_le p hi h0 hH T t))⟩
    have hh := initialCapacity_monotone p hi h0 hH hv.2
    rw [slitCapacityTime_capacity p hi h0 hH T ht] at hh
    change initialCapacity p hi h0 hH v/2 ≤ (t:ℝ)
    linarith

noncomputable def slitCapacityDriver (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) : Target.Driver := by
  refine ⟨⟨fun t => capacityDriverOnPrefix p hi h0 hH T hT (2*(t:ℝ)),
    (capacityDriverOnPrefix_continuous p hi h0 hH hT).comp
      (continuous_const.mul continuous_subtype_val)⟩,?_⟩
  change initialDrivingValue p hi h0 hH (slitCapacityTime p hi h0 hH T 0)
    ((slitCapacityTime_le p hi h0 hH T 0).trans_lt hT)=0
  simp only [slitCapacityTime_zero,initialDrivingValue_zero]

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.SlitRawForward
import OAI.Probability.SLE.Loewner.TargetInverseProperties

namespace OAI

/-! Exact raw inverse and surviving set for the constructed finite slit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem slitCapacityInverse_eq_raw (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) {w : ℂ} (hw : w∈upperHalfPlane) :
    Target.inverseFlow 1 (slitCapacityDriver p hi h0 hH hT) t w=
      slitCapacityInverse p hi h0 hH T t w := by
  have hz := initialInverseChart_mem_domain p hi h0 hH (slitCapacityTime p hi h0 hH T t) hw
  obtain ⟨hs,he⟩ := slitCapacityForward_eq_raw p hi h0 hH hT ht hz
  apply Target.inverseFlow_eq_of_surviving 1 _ t t.coe_nonneg _ w hs
  exact he.trans (initialForward_inverse p hi h0 hH _ hw)

theorem slitCapacity_surviving_eq (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    {z | Target.Surviving 1 (slitCapacityDriver p hi h0 hH hT) z t}=
      upperHalfPlane \ range (initialSubarc p (slitCapacityTime p hi h0 hH T t)) := by
  ext z
  constructor
  · intro hz
    have hw := Target.surviving_flow_mem_upperHalfPlane 1 _ z t t.coe_nonneg hz
    have he := Target.inverseFlow_eq_of_surviving 1 (slitCapacityDriver p hi h0 hH hT)
      t t.coe_nonneg z _ hz rfl
    rw [slitCapacityInverse_eq_raw p hi h0 hH hT ht hw] at he
    rw [← he]
    exact initialInverseChart_mem_domain p hi h0 hH _ hw
  · intro hz
    exact (slitCapacityForward_eq_raw p hi h0 hH hT ht hz).1

end SLEExactGauge

end

end OAI

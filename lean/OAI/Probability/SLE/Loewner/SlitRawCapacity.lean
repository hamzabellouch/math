import OAI.Probability.SLE.Loewner.SlitTailDomain
import OAI.Probability.SLE.Loewner.RawForwardInfinity

namespace OAI

/-! Every prescribed simple arc prefix, extended by a vertical image,
has an actual global capacity-two witness with its exact raw maps. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem RegularSLEPresentation.slit_raw_capacity_witness
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (hκ : 0<κ)
    (p : C(unitInterval,ℂ)) (hi : Function.Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT0 : 0<T) (hT : T<1) :
    let b := slitCapacityDriver p hi h0 hH hT
    IsCapacityTwoWitness b (fun s : ℝ≥0 => Target.trace 1 b s)
      (fun t z => Target.flow 1 b z t) (fun t => Target.inverseFlow 1 b t) := by
  dsimp only
  let b := slitCapacityDriver p hi h0 hH hT
  have hdom := a.slitCapacity_raw_domains hκ p hi h0 hH hT0 hT
  obtain ⟨hc,hz,_,hpos,_⟩ := a.slitCapacity_raw_geometry hκ p hi h0 hH hT0 hT
  refine ⟨hc,hz,?_,?_,a.raw_inverse_holomorphic hκ b,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t
    by_cases ht : 0<t
    · exact (show 0<(Target.trace 1 b t).im from hpos t ht).le
    · have he : t=0 := le_antisymm (le_of_not_gt ht) zero_le
      rw [he,hz]
      exact le_rfl
  · intro t
    rw [←hdom t]
    exact a.raw_forward_holomorphic hκ b t
  · intro t z hz
    exact Target.surviving_flow_mem_upperHalfPlane 1 b z t t.coe_nonneg
      (by simpa only [←hdom t,Set.mem_ofPred_eq] using hz)
  · intro t z hz
    rw [←hdom t]
    exact Target.inverseFlow_surviving 1 (by norm_num) b t z hz
  · intro t z hz
    exact Target.inverseFlow_eq_of_surviving 1 b t t.coe_nonneg z _
      (by simpa only [←hdom t,Set.mem_ofPred_eq] using hz) rfl
  · intro t z hz
    exact Target.flow_inverseFlow 1 (by norm_num) b t z hz
  · intro z hz
    exact Target.flow_zero 1 b z hz
  · intro t z hz
    have hs : Target.Surviving 1 b z t := by simpa only [←hdom t,Set.mem_ofPred_eq] using hz
    have hd := Target.flow_hasDerivWithinAt_of_survival b z t.coe_nonneg hs
    have he : (fun u : ℝ => Target.flow 1 b z (u.toNNReal:ℝ))
        =ᶠ[𝓝[Ici 0] (t:ℝ)] Target.flow 1 b z := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [Real.coe_toNNReal u hu]
    have hh := hd.congr_of_eventuallyEq he (by simp)
    simpa [Target.driverValue] using hh
  · intro t
    simpa only [b,hdom t] using Target.flow_hydrodynamic_normalization b t
  · exact slitCapacity_radial_limit p hi h0 hH hT

end SLEExactGauge

end

end OAI

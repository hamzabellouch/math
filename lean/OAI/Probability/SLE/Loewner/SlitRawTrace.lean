import OAI.Probability.SLE.Loewner.SlitRawInverse
import OAI.Probability.SLE.Loewner.SlitPhysicalTrace

namespace OAI

/-! The exact raw trace of the continuous based driver is the prescribed
simple slit throughout its capacity-two prefix. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem slitCapacity_raw_trace_eq (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    Target.trace 1 (slitCapacityDriver p hi h0 hH hT) t=
      slitCapacityCurve p hi h0 hH T t := by
  let s := slitCapacityTime p hi h0 hH T t
  have hs : s<1 := (slitCapacityTime_le p hi h0 hH T t).trans_lt hT
  have htip := initialInverse_radial_driver_limit p hi h0 hH hs
  have he : slitCapacityDriver p hi h0 hH hT t=initialDrivingValue p hi h0 hH s hs := rfl
  have hr : Tendsto (fun y : ℝ => Target.inverseFlow 1 (slitCapacityDriver p hi h0 hH hT) t
      ((slitCapacityDriver p hi h0 hH hT t:ℂ)+(y:ℂ)*I)) (𝓝[>] (0:ℝ)) (𝓝 (p s)) := by
    apply htip.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hw : (slitCapacityDriver p hi h0 hH hT t:ℂ)+(y:ℂ)*I∈upperHalfPlane := by
      simpa [upperHalfPlane] using hy
    rw [slitCapacityInverse_eq_raw p hi h0 hH hT ht hw]
    rfl
  simpa only [Target.trace,one_mul,Target.driverValue,Real.toNNReal_coe,slitCapacityCurve,s] using
    hr.limUnder_eq

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Loewner.SlitClockRestriction

namespace OAI

/-! Every point surviving to a chosen physical time follows the exact
Loewner equation on the whole interval up to that time. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem slitCapacityForward_derivative_upto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p (slitCapacityTime p hi h0 hH T t)))
    {u : ℝ} (hu : u∈Icc 0 (t:ℝ)) :
    HasDerivWithinAt (fun v : ℝ => slitCapacityForward p hi h0 hH T v.toNNReal z)
      (2/(slitCapacityForward p hi h0 hH T u.toNNReal z-
        (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ))) (Icc 0 (t:ℝ)) u := by
  let S := slitCapacityTime p hi h0 hH T t
  have hST : S ≤ T := slitCapacityTime_le p hi h0 hH T t
  have hS : S<1 := hST.trans_lt hT
  have hHS : slitCapacityHorizon p hi h0 hH S=t := slitCapacityHorizon_time p hi h0 hH T ht
  have hu' : u.toNNReal ≤ slitCapacityHorizon p hi h0 hH S := by
    rw [hHS]
    exact Real.toNNReal_le_iff_le_coe.mpr hu.2
  have hd := slitCapacityForward_prefix_derivative p hi h0 hH hS hz hu'
  rw [hHS,Real.coe_toNNReal u hu.1] at hd
  have hG (v : ℝ) (hv : v∈Icc 0 (t:ℝ)) :
      slitCapacityForward p hi h0 hH T v.toNNReal z=
        slitCapacityForward p hi h0 hH S v.toNNReal z := by
    rw [slitCapacityForward_restrict p hi h0 hH hST]
    rw [hHS]
    exact Real.toNNReal_le_iff_le_coe.mpr hv.2
  have hres := hd.congr hG (hG u hu)
  rw [← hG u hu,← slitCapacityDriver_restrict p hi h0 hH hST hT hu'] at hres
  exact hres

end SLEExactGauge

end

end OAI

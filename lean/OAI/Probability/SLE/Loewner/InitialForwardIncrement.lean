import OAI.Probability.SLE.Loewner.FutureCapacityAdditive

namespace OAI

/-! Exact capacity increments control forward-map motion on the common
surviving domain. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialForward_increment_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p t)) :
    ‖initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z‖≤
      (initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s)/
        (initialForwardChart p hi h0 hH t z).im := by
  let Q := futureSlitChart p hi h0 hH hst ht
  let U := initialDrivingValue p hi h0 hH s (hst.trans ht)
  let w := initialForwardChart p hi h0 hH s z-(U:ℂ)
  have hw : w∈upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht) :=
    (initialForward_centered_bijOn p hi h0 hH hst ht).mapsTo hz
  have hc : Q.capacity=initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s :=
    futureSlitChart_capacity_eq p hi h0 hH hst ht
  have he : (U:ℂ)+Q.forward w=initialForwardChart p hi h0 hH t z :=
    futureComposedForward_eq p hi h0 hH hst ht hz
  have him : (Q.forward w).im=(initialForwardChart p hi h0 hH t z).im := by
    simpa only [add_im,ofReal_im,zero_add] using congrArg Complex.im he
  have hd : Q.forward w-w=
      initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z := by
    dsimp only [w] at he ⊢
    linear_combination he
  have hb := Q.forward_displacement hw
  rwa [hc,him,hd] at hb

theorem initialForward_height_antitone (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s≤t) (ht : t<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p t)) :
    (initialForwardChart p hi h0 hH t z).im≤(initialForwardChart p hi h0 hH s z).im := by
  obtain rfl | hst := hst.eq_or_lt
  · exact le_rfl
  let Q := futureSlitChart p hi h0 hH hst ht
  let U := initialDrivingValue p hi h0 hH s (hst.trans ht)
  have hw := (initialForward_centered_bijOn p hi h0 hH hst ht).mapsTo hz
  have hb := Q.height_le _ hw
  have he : (U:ℂ)+Q.forward (initialForwardChart p hi h0 hH s z-(U:ℂ))=
      initialForwardChart p hi h0 hH t z := futureComposedForward_eq p hi h0 hH hst ht hz
  have him := congrArg Complex.im he
  simp only [add_im,ofReal_im,zero_add,sub_im,sub_zero] at hb him
  rwa [← him]

end SLEExactGauge

end

end OAI

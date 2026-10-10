import OAI.Probability.SLE.Loewner.SlitCapacityQuotient
import OAI.Probability.SLE.Loewner.InitialForwardIncrement
import OAI.Probability.SLE.Loewner.FutureSlitRadius

namespace OAI

/-! The exact chart composition turns the static small-slit estimate
into an estimate for the evolving map's capacity difference quotient. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem initialForward_quotient_kernel (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p t))
    {R : ℝ} (hR : 0<R)
    (hp : ∀ u : unitInterval, ‖centeredFutureArc p hi h0 hH hst ht u‖<R)
    (hn : 2*R≤‖initialForwardChart p hi h0 hH s z-
      (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)‖) :
    ‖(initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z)/
        ((initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s:ℝ):ℂ)-
      1/(initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ))‖≤
      10*R/‖initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)‖^2 := by
  let Q := futureSlitChart p hi h0 hH hst ht
  let U := initialDrivingValue p hi h0 hH s (hst.trans ht)
  let w := initialForwardChart p hi h0 hH s z-(U:ℂ)
  have hw : w∈upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht) :=
    (initialForward_centered_bijOn p hi h0 hH hst ht).mapsTo hz
  have hb := Q.forward_quotient_kernel
    (centeredFutureArc_injective p hi h0 hH hst ht)
    (centeredFutureArc_zero p hi h0 hH hst ht)
    (fun _ hu => centeredFutureArc_upper p hi h0 hH hst ht hu) hR hp hw.1 hn
  have he : (U:ℂ)+Q.forward w=initialForwardChart p hi h0 hH t z :=
    futureComposedForward_eq p hi h0 hH hst ht hz
  have hd : Q.forward w-w=
      initialForwardChart p hi h0 hH t z-initialForwardChart p hi h0 hH s z := by
    dsimp only [w] at he ⊢
    linear_combination he
  rwa [hd,show Q.capacity=_ from futureSlitChart_capacity_eq p hi h0 hH hst ht] at hb

end SLEExactGauge

end

end OAI

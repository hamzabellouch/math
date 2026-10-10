import OAI.MathematicalPhysics.Boltzmann.Branching.HotRatioCollisionTrace
import OAI.MathematicalPhysics.Boltzmann.Branching.OffAxisBoxExhaustion
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEscapingSeed

namespace OAI

/-! # Full-density vanishing contradicts the actual cap nonvanishing theorem -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.full_vanishing_impossible (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hfinite : E.horizon < ⊤)
    (hfull : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
      (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0)) : False := by
  apply E.nonvanishing hcarleman hMityagin hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  intro A hA hAmax R
  have hz := ae_zero_time_slab_of_boxes (A := A) (fun B hB ε hε =>
    E.full_vanishing_implies_zero_box hs₀ hsmax hη hηmax hK hd₀.le (by linarith) hq₂
      hfinite hfull hA.le hAmax hB hε)
  rw [EuclideanFlight.hotBaseVolume_eq,← Measure.restrict_univ (μ := (volume : Measure Velocity)),
    Measure.prod_restrict,← Measure.volume_eq_prod]
  filter_upwards [ae_restrict_of_ae hz,
    ae_restrict_mem ((EuclideanFlight.hotBaseSet_measurable A R).prod MeasurableSet.univ)] with z hz hm
  exact hz hm.1.1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI

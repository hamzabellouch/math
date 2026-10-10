import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumEndpointTransport

namespace OAI

/-! # Physical gain histories in the characteristic coordinates of the hot balance -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamCharacteristicKernel (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  transportedKernel (flightCharacteristicEquiv endTime).symm (physicalBeamCollision b endTime)

instance beamCharacteristicKernel_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (beamCharacteristicKernel b endTime) := by
  unfold beamCharacteristicKernel
  infer_instance

theorem physicalBeamEvent_transport (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    physicalBeamEvent b endTime C = transportedKernel (flightCharacteristicEquiv endTime)
      (beamCharacteristicKernel b endTime ∘ₖ WeakTime.residenceKernel C endTime) := by
  unfold physicalBeamEvent
  rw [transportedKernel_compKernel,← physicalWaitingKernel_eq_transport]
  rw [beamCharacteristicKernel,transportedKernel_symm]

theorem physicalBeamEvent_pow_transport (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) :
    (physicalBeamEvent b endTime C)^n = transportedKernel (flightCharacteristicEquiv endTime)
      ((beamCharacteristicKernel b endTime ∘ₖ WeakTime.residenceKernel C endTime)^n) := by
  rw [transportedKernel_pow,← physicalBeamEvent_transport]

theorem physical_terminal_characteristic (endTime : ℝ) (C : ℝ≥0)
    (f : V × V → ℝ≥0∞) (p : PhysicalFlightState) :
    clockSurvival C p.1 * f (finishMediumFlight p) =
      ENNReal.ofReal (Real.exp ((C:ℝ)*((flightCharacteristicEquiv endTime p).1-endTime))) *
        f (EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2) := by
  have hx : EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2 =
      finishMediumFlight p := by
    apply Prod.ext
    · dsimp [EuclideanFlight.flight,flightCharacteristicEquiv,finishMediumFlight]
      module
    · rfl
  rw [hx]
  unfold clockSurvival
  congr 3
  dsimp [flightCharacteristicEquiv]
  ring

theorem physicalGainEndpoint_characteristic (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState) :
    physicalGainEndpoint b endTime C n p =
      ((WeakTime.phaseEndpointKernel C endTime ∘ₖ
        ((beamCharacteristicKernel b endTime ∘ₖ WeakTime.residenceKernel C endTime)^n))
          (flightCharacteristicEquiv endTime p)).map (EuclideanFlight.flight endTime) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hg : Measurable (fun z => f (EuclideanFlight.flight endTime z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving endTime).measurable
  have hw : Measurable (fun q : PhysicalFlightState => clockSurvival C q.1*f (finishMediumFlight q)) :=
    (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)
  rw [physicalGainEndpoint_lintegral b endTime C n p hf,
    physicalBeamEvent_pow_transport,transportedKernel_lintegral _ _ _ hw,
    lintegral_map hf (EuclideanFlight.flight_measurePreserving endTime).measurable,
    Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,physical_terminal_characteristic endTime C f]
  simp only [MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI

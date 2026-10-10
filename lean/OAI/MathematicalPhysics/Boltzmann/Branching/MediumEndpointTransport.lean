import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.TransportedKernelRestriction
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGlobalRenormalized

namespace OAI

section

/-! # Each marked event is damped free waiting followed by physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumEventKernel_eq_comp (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    mediumEventKernel b endTime T p =
      (mediumStateCollision b endTime ∘ₖ physicalWaitingKernel referenceClock) p := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [mediumEventKernel_physical_lintegral b endTime p hT hF,
    Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral referenceClock p hF.lintegral_kernel]
  apply lintegral_congr
  intro s
  rw [mediumStateCollision_lintegral b endTime _ hF]
  simp only [physicalAdvance,mediumPoint]
  rw [show endTime-(p.1-s) = endTime-p.1+s by ring]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite marked histories are iterated physical waiting and collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumEventKernel_remaining_le (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂mediumEventKernel b endTime T p, q.1 ≤ p.1 := by
  rw [ae_iff]
  let A : Set PhysicalFlightState := {q | ¬q.1 ≤ p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change mediumEventKernel b endTime T p A = 0
  rw [← lintegral_indicator_one hA,
    mediumEventKernel_physical_lintegral b endTime p hT
      (F := A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsp : p.1-s ≤ p.1 := sub_le_self _ hs.1.le
  have hz : ∀ v : V, A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      (p.1-s,((mediumPoint endTime p s).2,v)) = 0 := by
    intro v
    exact indicator_of_notMem (by simpa only [A,mem_ofPred_eq,not_not] using hsp) _
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem mediumEventKernel_pow_eq_comp (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((mediumEventKernel b endTime T)^n) p =
      ((mediumStateCollision b endTime ∘ₖ physicalWaitingKernel referenceClock)^n) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hpow (L : Kernel PhysicalFlightState PhysicalFlightState) :
        L^(n+1) = (L^n) ∘ₖ L := by
      simpa only [pow_one] using Kernel.pow_add L n 1
    rw [hpow,hpow,Kernel.comp_apply,Kernel.comp_apply]
    calc
      (mediumEventKernel b endTime T p).bind ((mediumEventKernel b endTime T)^n) =
          (mediumEventKernel b endTime T p).bind
            ((mediumStateCollision b endTime ∘ₖ physicalWaitingKernel referenceClock)^n) := by
        apply Measure.bind_congr_right
        filter_upwards [mediumEventKernel_remaining_le b endTime p hT] with q hq
        exact ih q (hq.trans hT)
      _ = _ := by rw [mediumEventKernel_eq_comp b endTime p hT]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical marked histories in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalWaitingKernel_eq_transport (C : ℝ≥0) (endTime : ℝ) :
    physicalWaitingKernel C = transportedKernel (flightCharacteristicEquiv endTime)
      (WeakTime.residenceKernel C endTime) := by
  apply Kernel.ext_fun
  intro p f hf
  rw [transportedKernel_lintegral _ _ p hf]
  have H := flightCharacteristic_waiting_lintegral C endTime p
    (F := fun z => f ((flightCharacteristicEquiv endTime).symm z))
    (hf.comp (flightCharacteristicEquiv endTime).symm.measurable)
  simpa only [MeasurableEquiv.symm_apply_apply] using H

def mediumCharacteristicKernel (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  transportedKernel (flightCharacteristicEquiv endTime).symm (mediumStateCollision b endTime)

instance mediumCharacteristicKernel_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (mediumCharacteristicKernel b endTime) := by
  unfold mediumCharacteristicKernel
  infer_instance

theorem mediumStateCollision_eq_transport (b : BeamCoefficients) (endTime : ℝ) :
    mediumStateCollision b endTime = transportedKernel (flightCharacteristicEquiv endTime)
      (mediumCharacteristicKernel b endTime) :=
  (transportedKernel_symm (flightCharacteristicEquiv endTime) _).symm

theorem mediumEventKernel_pow_characteristic (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((mediumEventKernel b endTime T)^n) p =
      transportedKernel (flightCharacteristicEquiv endTime)
        ((mediumCharacteristicKernel b endTime ∘ₖ
          WeakTime.residenceKernel referenceClock endTime)^n) p := by
  rw [mediumEventKernel_pow_eq_comp b endTime n p hT,
    mediumStateCollision_eq_transport b endTime,
    physicalWaitingKernel_eq_transport referenceClock endTime,
    ← transportedKernel_compKernel,← transportedKernel_pow]

theorem mediumCharacteristicKernel_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (z : ℝ × WeakTime.Phase) {f : ℝ × WeakTime.Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂mediumCharacteristicKernel b endTime z) =
      ∫⁻ v, f (z.1,(z.2.1+z.1 • z.2.2-z.1 • v,v))
        ∂mediumCollisionKernel b ((z.1,z.2.1+z.1 • z.2.2),z.2.2) := by
  have hc : Measurable (fun q => f (flightCharacteristicEquiv endTime q)) :=
    hf.comp (flightCharacteristicEquiv endTime).measurable
  rw [mediumCharacteristicKernel,transportedKernel_lintegral _ _ z hf]
  simp only [MeasurableEquiv.symm_symm]
  rw [mediumStateCollision_lintegral b endTime _ hc]
  simp only [flightCharacteristicEquiv,MeasurableEquiv.symm_mk,MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,sub_sub_cancel]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Terminal physical history measures and characteristic endpoint histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumFlightSeed_characteristic (endTime : ℝ) (f : V × V → ℝ≥0∞)
    (p : PhysicalFlightState) :
    mediumFlightSeed f p =
      ENNReal.ofReal (Real.exp ((referenceClock : ℝ)*
        ((flightCharacteristicEquiv endTime p).1-endTime))) *
      f (EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2) := by
  have hx : EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2 =
      finishMediumFlight p := by
    apply Prod.ext
    · dsimp [EuclideanFlight.flight,flightCharacteristicEquiv,finishMediumFlight]
      module
    · rfl
  rw [hx]
  unfold mediumFlightSeed clockSurvival
  congr 3
  dsimp [flightCharacteristicEquiv]
  ring

theorem mediumEndpointKernel_characteristic (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    mediumEndpointKernel b endTime T n p =
      ((WeakTime.phaseEndpointKernel referenceClock endTime ∘ₖ
        ((mediumCharacteristicKernel b endTime ∘ₖ
          WeakTime.residenceKernel referenceClock endTime)^n))
          (flightCharacteristicEquiv endTime p)).map (EuclideanFlight.flight endTime) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hg : Measurable (fun z => f (EuclideanFlight.flight endTime z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving endTime).measurable
  rw [mediumEndpointKernel_lintegral b endTime T n p hf,
    mediumEventKernel_pow_characteristic b endTime n p hT,
    transportedKernel_lintegral _ _ _ (mediumFlightSeed_measurable hf),
    lintegral_map hf (EuclideanFlight.flight_measurePreserving endTime).measurable,
    Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,
    mediumFlightSeed_characteristic endTime f]
  simp only [MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI

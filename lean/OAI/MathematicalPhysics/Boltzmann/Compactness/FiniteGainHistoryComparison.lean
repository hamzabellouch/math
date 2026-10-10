import OAI.MathematicalPhysics.Boltzmann.Jets.BeamGainNormalOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteDepthKernelOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGainStrictTime
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGainStrictTime
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedBlockComparison

namespace OAI

/-! # Every fixed finite physical gain history is dominated by the actual localized histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finite_gain_history_le_localized_window
    (b : BeamCoefficients) (C : ℝ≥0) (T a η l h R : ℝ) (N : ℕ) (x v : V)
    (hh : 0 ≤ h) (hv : ‖v‖ ≤ R)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q → flightCharacteristicEquiv T q ∈ Ω)
    (hpartner : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2 ∧ ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hlocal : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q))) :
    ((physicalBeamEvent b T C)^N) (h,(x,v)) ≤
      ((localizedNormalWindowEvent b 1 C T a η l (T-h) hΩ)^N) (h,(x,v)) := by
  let D := fun n q => finiteFlightCone N n h R x q
  apply kernel_pow_le_on_depth (physicalBeamEvent b T C)
    (localizedNormalWindowEvent b 1 C T a η l (T-h) hΩ) D N _ _ N le_rfl
      (h,(x,v)) (finiteFlightCone_initial hh x v hv)
  · intro n hn p hp
    exact physicalBeamEvent_ae_finiteCone b T C hp
      (fun q hq => (hpartner (n+1) hn q hq).1)
      (fun q hq => (hpartner (n+1) hn q hq).2)
  · intro n hn p hp
    have hle : physicalBeamEvent b T C p ≤
        localizedNormalPhysicalEvent b 1 C T a η l hΩ p := by
      change (physicalBeamCollision b T ∘ₖ physicalWaitingKernel C) p ≤
        (localizedNormalCollision b 1 C T a η l hΩ ∘ₖ physicalWaitingKernel (Real.toNNReal C)) p
      rw [Real.toNNReal_coe]
      apply KernelHistoryOrder.measure_comp_mono_ae _ le_rfl
      filter_upwards [physicalWaitingKernel_ae_finiteCone C hp] with q hq
      obtain ⟨hz,hdp,hdm⟩ := hlocal (n+1) hn q hq
      apply physicalBeamCollision_le_localized b T C a η l hΩ q hz hdp hdm
      filter_upwards [physicalBeamCollision_ae_finiteCone b T hq
        (hpartner (n+1) hn q hq).1 (hpartner (n+1) hn q hq).2] with r hr
      exact hΩcone n (Nat.le_of_lt hn) r hr
    calc
      _ = (physicalBeamEvent b T C p).restrict (physicalCollisionWindow (T-h) T) :=
        (Measure.restrict_eq_self_of_ae_mem (physicalBeamEvent_ae_time_window b T h C hp.2.1)).symm
      _ ≤ _ := Measure.restrict_mono_measure hle _

theorem finite_gain_endpoint_le_localized
    (b : BeamCoefficients) (C : ℝ≥0) (T a η l h R : ℝ) (N : ℕ) (x v : V)
    (hh : 0 ≤ h) (hv : ‖v‖ ≤ R)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q → flightCharacteristicEquiv T q ∈ Ω)
    (hpartner : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2 ∧ ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hlocal : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    {A : Set (V × V)} (hA : MeasurableSet A) :
    physicalGainEndpoint b T C N (h,(x,v)) A ≤
      (WeakTime.phaseEndpointKernel C T ∘ₖ
        ((((localizedNormalBeamKernel b 1 C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc (T-h) T))) ∘ₖ
            WeakTime.residenceKernel C T)^N))
        (flightCharacteristicEquiv T (h,(x,v))) (flight T ⁻¹' A) := by
  rw [physicalGainEndpoint_apply b T C N _ hA]
  have hle := lintegral_mono' (finite_gain_history_le_localized_window b C T a η l h R N x v
    hh hv hΩ hΩcone hpartner hlocal) (le_refl
      (fun q : PhysicalFlightState => clockSurvival C q.1*A.indicator 1 (finishMediumFlight q)))
  have heq := localizedNormal_endpoint_characteristic b 1 C T a η l (T-h) hΩ N
    (h,(x,v)) (f := A.indicator (1 : V × V → ℝ≥0∞))
    (measurable_const.indicator hA)
  apply hle.trans_eq
  rw [heq,← lintegral_indicator_one ((flight_measurePreserving T).measurable hA)]
  apply lintegral_congr
  intro q
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI

import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedEntryPortion
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBoundedEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedLateBoxPhysicalBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance

namespace OAI

section

/-! # Retaining the actual open-left collision-time window in physical histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalCollisionWindow (s T : ℝ) : Set PhysicalFlightState := {p | T-p.1 ∈ Ioc s T}

theorem physicalCollisionWindow_measurable (s T : ℝ) : MeasurableSet (physicalCollisionWindow s T) :=
  (measurable_const.sub measurable_fst) measurableSet_Ioc

def localizedNormalWindowEvent (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (localizedNormalPhysicalEvent b ρ C T a η l hΩ).restrict (physicalCollisionWindow_measurable s T)

instance localizedNormalWindowEvent_sFinite (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalWindowEvent b ρ C T a η l s hΩ) := by
  unfold localizedNormalWindowEvent
  infer_instance

theorem localizedNormalWindowEvent_transport (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    localizedNormalWindowEvent b ρ C T a η l s hΩ =
      transportedKernel (flightCharacteristicEquiv T)
        (((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T) := by
  rw [transportedKernel_compKernel,transportedKernel_restrict,
    ← physicalWaitingKernel_eq_transport,Kernel.comp_restrict]
  simp only [localizedNormalWindowEvent,localizedNormalPhysicalEvent,localizedNormalCollision,
    Real.toNNReal_coe]
  rfl

theorem boundedHistory_le_localized_window {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (p : PhysicalFlightState) (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6)
    (hΩcone : ∀ q, boundedFlightCone p q → flightCharacteristicEquiv T q ∈ Ω)
    (hlocal : ∀ q, boundedFlightCone p q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      characteristicBeamFrequency b (flightCharacteristicEquiv T q) ≤ (referenceClock:ℝ))
    (n : ℕ) :
    ((dampedBoundedDensityScaledEvent C b T ρ)^n) p ≤
      ((localizedNormalWindowEvent b ρ (ρ*C) T a η l (T-p.1) hΩ)^n) p := by
  apply kernel_pow_le_on_invariant _ _ {q | boundedFlightCone p q} _ _ n p
    (boundedFlightCone_refl ht hv)
  · intro q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b T ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr
  · intro q hq
    have he : dampedBoundedDensityScaledEvent C b T ρ q ≤
        localizedNormalPhysicalEvent b ρ (ρ*C) T a η l hΩ q := by
      simpa only [pow_one] using boundedHistory_le_localized hC b ρ T a η l hΩ q hq.1 hq.2.2.1
        (fun r hr => hΩcone r (boundedFlightCone_trans hq hr))
        (fun r hr => hlocal r (boundedFlightCone_trans hq hr)) 1
    have htwin : ∀ᵐ r ∂dampedBoundedDensityScaledEvent C b T ρ q,
        r ∈ physicalCollisionWindow (T-p.1) T :=
      dampedBoundedDensityScaledEvent_ae_time_window C b T ρ hq
    calc
      _ = (dampedBoundedDensityScaledEvent C b T ρ q).restrict
          (physicalCollisionWindow (T-p.1) T) := (Measure.restrict_eq_self_of_ae_mem htwin).symm
      _ ≤ _ := Measure.restrict_mono_measure he _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical normal-angle histories end at the hot trace's characteristic endpoint -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localizedNormalWindowEvent_pow_transport (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (n : ℕ) :
    (localizedNormalWindowEvent b ρ C T a η l s hΩ)^n =
      transportedKernel (flightCharacteristicEquiv T)
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Set.Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T)^n) := by
  rw [transportedKernel_pow,← localizedNormalWindowEvent_transport]

theorem localizedNormal_endpoint_characteristic (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (n : ℕ) (p : PhysicalFlightState) {f : V × V → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, clockSurvival C q.1*f (finishMediumFlight q)
      ∂((localizedNormalWindowEvent b ρ C T a η l s hΩ)^n) p) =
    ∫⁻ q, f (EuclideanFlight.flight T q)
      ∂(WeakTime.phaseEndpointKernel C T ∘ₖ
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Set.Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T)^n)) (flightCharacteristicEquiv T p) := by
  have hg : Measurable (fun z => f (EuclideanFlight.flight T z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving T).measurable
  have hw : Measurable (fun q : PhysicalFlightState => clockSurvival C q.1*f (finishMediumFlight q)) :=
    (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)
  rw [localizedNormalWindowEvent_pow_transport,transportedKernel_lintegral _ _ _ hw,
    Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,physical_terminal_characteristic T C f]
  simp only [MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The finite physical branching block lies below the actual angular endpoint histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedHistoryBlockMass (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (A : Set (V × V))
    (N : ℕ) (z : ℝ × WeakTime.Phase) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ q, A.indicator 1 (EuclideanFlight.flight T q)
    ∂(WeakTime.phaseEndpointKernel C T ∘ₖ
      ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
        (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
          WeakTime.residenceKernel C T)^n)) z

theorem physicalBlock_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (s Δ a η l κ d : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (x : V) (v : RetainedState)
    (hΔ : 0 ≤ Δ) (hv : ‖(v:V)‖ ≤ 6) (hp : (x,(v:V)) ∈ lateBox κ d s)
    (hΩcone : ∀ q, boundedFlightCone (Δ,(x,(v:V))) q → flightCharacteristicEquiv (s+Δ) q ∈ Ω)
    (hlocal : ∀ q, boundedFlightCone (Δ,(x,(v:V))) q →
      flightCharacteristicEquiv (s+Δ) q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv (s+Δ) q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv (s+Δ) q)) ∧
      characteristicBeamFrequency b (flightCharacteristicEquiv (s+Δ) q) ≤ (referenceClock:ℝ))
    (N : ℕ) :
    dampedDensityScaledBlockMass C b (s+Δ) ρ x Δ v κ d N ≤
      localizedHistoryBlockMass b ρ (ρ*C) (s+Δ) a η l s hΩ (lateBox κ d (s+Δ)) N
        (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V)))) := by
  let A := lateBox κ d (s+Δ)
  have hA : MeasurableSet A := lateBox_measurable _ _ _
  have hf : Measurable (A.indicator (1 : V × V → ℝ≥0∞)) := measurable_const.indicator hA
  unfold dampedDensityScaledBlockMass localizedHistoryBlockMass
  simp only [Real.toNNReal_coe]
  apply Finset.sum_le_sum
  intro n _hn
  have hle := boundedHistory_le_localized_window hC b ρ (s+Δ) a η l hΩ
    (Δ,(x,(v:V))) hΔ hv hΩcone hlocal n
  have htime : (s+Δ)-Δ = s := by ring
  rw [htime] at hle
  calc
    _ ≤ ∫⁻ q, clockSurvival (ρ*C) q.1*A.indicator 1 (finishMediumFlight q)
        ∂((dampedBoundedDensityScaledEvent C b (s+Δ) ρ)^n) (Δ,(x,(v:V))) := by
      apply lintegral_mono
      intro q
      dsimp only
      gcongr
      exact fun _ hy => physicalBlockTarget_subset_lateBox hp hy
    _ ≤ ∫⁻ q, clockSurvival (ρ*C) q.1*A.indicator 1 (finishMediumFlight q)
        ∂((localizedNormalWindowEvent b ρ (ρ*C) (s+Δ) a η l s hΩ)^n) (Δ,(x,(v:V))) :=
      lintegral_mono' hle le_rfl
    _ = _ := by
      simpa only [NNReal.coe_mul] using
        localizedNormal_endpoint_characteristic b ρ (ρ*C) (s+Δ) a η l s hΩ n (Δ,(x,(v:V))) hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI

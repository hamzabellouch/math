import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedCollisionHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledBoundedEvent
import OAI.MathematicalPhysics.Boltzmann.Branching.TransportedKernelRestriction
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelConjugacy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGainTransport
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricAnnularFrequency
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention

namespace OAI

section

/-! # The measurable two-beam collision law under local density normalization -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumCollision_normalized (C : ℝ≥0) (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V)
    (z : MediumState) :
    dampedMediumCollision C (b.normalized ρ t₀ x₀) z =
      dampedMediumCollision C b (normalizedPoint ρ t₀ x₀ z.1,z.2) := by
  rw [dampedMediumCollision_apply,dampedMediumCollision_apply,mediumCollisionKernel_normalized]

theorem dampedMediumStateCollision_scale_map (C : ℝ≥0) (b : BeamCoefficients) (ρ : ℝ) (hρ : ρ ≠ 0)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedMediumStateCollision C b endTime p).map (flightScaleEquiv ρ hρ x₀) =
      dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hc : Measurable (fun q => F (flightScaleEquiv ρ hρ x₀ q)) :=
    hF.comp (flightScaleEquiv ρ hρ x₀).measurable
  rw [lintegral_map hF (flightScaleEquiv ρ hρ x₀).measurable,
    dampedMediumStateCollision_lintegral C b endTime p hc,
    dampedMediumStateCollision_lintegral C _ _ _ hF,
    dampedMediumCollision_normalized,normalized_flight_location]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One finite collision depth works throughout each expanding late box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_damped_lateBox_geometric_block {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ Dmax : ℝ≥0, ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η α γ K t : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t →
      ∀ (x : V) (v : RetainedState), (x,(v : V)) ∈ lateBox κ d t →
      let ρ := K/(4*‖transverse x‖)
      let A := ρ*((8*κ*A₀/K)*t)
      (6 : ℝ≥0∞) < dampedBoundedBlockMass D
        ((GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖).normalized ρ t x)
        A (4*A₀) (A,(0,v)) κ d N := by
  have hC : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨A₀,hA₀,hblock⟩ := GeometricBackground.geometric_damped_bounded_block_growth
    hd (by linarith) hκ hκsmall hg hC
  refine ⟨A₀,hA₀,?_⟩
  intro Dmax
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock (4*A₀) (by linarith) Dmax
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η α γ K t hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp
  obtain ⟨hr,htime,hax⟩ := lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp
  exact hgrowth D hD hDmax hθ hη hηsmall hr hα hαsmall hγ hγsmall hK hKlarge ht.le htime
    (lateBox_block_duration hκ ht hdsmall hK hA₀ hp) x v rfl hax

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Enlarged-damping physical histories in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  transportedKernel (flightCharacteristicEquiv endTime).symm (dampedMediumStateCollision C b endTime)

instance dampedCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedCharacteristicKernel C b endTime) := by
  unfold dampedCharacteristicKernel
  infer_instance

theorem dampedStateCollision_eq_transport (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    dampedMediumStateCollision C b endTime = transportedKernel (flightCharacteristicEquiv endTime)
      (dampedCharacteristicKernel C b endTime) :=
  (transportedKernel_symm (flightCharacteristicEquiv endTime) _).symm

theorem dampedEventKernel_pow_characteristic (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((dampedMediumEventKernel C b endTime T)^n) p =
      transportedKernel (flightCharacteristicEquiv endTime)
        ((dampedCharacteristicKernel C b endTime ∘ₖ
          WeakTime.residenceKernel C endTime)^n) p := by
  rw [damped_mediumEventKernel_pow_eq_comp C b endTime n p hT,
    dampedStateCollision_eq_transport C b endTime,
    physicalWaitingKernel_eq_transport C endTime,
    ← transportedKernel_compKernel,← transportedKernel_pow]

theorem dampedCharacteristicKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (z : ℝ × WeakTime.Phase) {f : ℝ × WeakTime.Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂dampedCharacteristicKernel C b endTime z) =
      ∫⁻ v, f (z.1,(z.2.1+z.1 • z.2.2-z.1 • v,v))
        ∂dampedMediumCollision C b ((z.1,z.2.1+z.1 • z.2.2),z.2.2) := by
  have hc : Measurable (fun q => f (flightCharacteristicEquiv endTime q)) :=
    hf.comp (flightCharacteristicEquiv endTime).measurable
  rw [dampedCharacteristicKernel,transportedKernel_lintegral _ _ z hf]
  simp only [MeasurableEquiv.symm_symm]
  rw [dampedMediumStateCollision_lintegral C b endTime _ hc]
  simp only [flightCharacteristicEquiv,MeasurableEquiv.symm_mk,MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,sub_sub_cancel]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The enlarged-damping characteristic kernel is gain plus positive retention -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicBeamFrequency (b : BeamCoefficients) (z : ℝ × WeakTime.Phase) : ℝ :=
  mediumFrequency z.2.2 (b.plusPartner (characteristicBeamPoint z))
    (b.minusPartner (characteristicBeamPoint z))
    (b.plusDensity (characteristicBeamPoint z)) (b.minusDensity (characteristicBeamPoint z))

theorem characteristicBeamFrequency_measurable (b : BeamCoefficients) :
    Measurable (characteristicBeamFrequency b) := by
  have hm : Measurable characteristicBeamPoint := by unfold characteristicBeamPoint; fun_prop
  have hp := b.plusPartner_measurable.comp hm
  have hn := b.minusPartner_measurable.comp hm
  have hdp := b.plusDensity_measurable.comp hm
  have hdn := b.minusDensity_measurable.comp hm
  unfold characteristicBeamFrequency mediumFrequency
  fun_prop

theorem dampedCharacteristicKernel_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (z : ℝ × WeakTime.Phase)
    (hf : characteristicBeamFrequency b z ≤ (referenceClock : ℝ)) :
    dampedCharacteristicKernel C b endTime z =
      positiveSourceKernel (beamCharacteristicKernel b endTime) (fun _ => 1)
        (fun q => (C : ℝ)-characteristicBeamFrequency b q) z := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (characteristicBeamJump z) := by unfold characteristicBeamJump; fun_prop
  have hj : Measurable (fun v => F (characteristicBeamJump z v)) := hF.comp hm
  rw [dampedCharacteristicKernel_lintegral C b endTime z hF]
  change (∫⁻ v, F (characteristicBeamJump z v)
    ∂dampedMediumCollision C b (characteristicBeamPoint z,z.2.2)) = _
  rw [dampedMediumCollision_eq_nonzero_marks hC b (characteristicBeamPoint z,z.2.2) hf,
    lintegral_add_measure,lintegral_add_measure,lintegral_smul_measure,
    mediumMarkedKernel_lintegral b 1 _ hj,mediumMarkedKernel_lintegral b 2 _ hj,
    lintegral_dirac,smul_eq_mul,
    positiveSourceKernel_one_lintegral (beamCharacteristicKernel b endTime)
      (r := fun q => (C : ℝ)-characteristicBeamFrequency b q) (measurable_const.sub
      (characteristicBeamFrequency_measurable b)) z hF,
    beamCharacteristicKernel_lintegral b endTime z hF]
  congr 1
  simp only [characteristicBeamJump,add_sub_cancel_right]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical collision intensity and clock normalize by the same density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedDensityScaledCollision (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumStateCollision C b endTime).withDensity (fun _ _ => ENNReal.ofReal (ρ : ℝ))

instance dampedDensityScaledCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedDensityScaledCollision C b endTime ρ) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

theorem dampedDensityScaledCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedDensityScaledCollision C b endTime ρ p) =
      ENNReal.ofReal (ρ : ℝ) * ∫⁻ q, F q ∂dampedMediumStateCollision C b endTime p := by
  rw [dampedDensityScaledCollision,Kernel.lintegral_withDensity _ (by fun_prop) p hF,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

def dampedDensityScaledEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  dampedDensityScaledCollision C b endTime ρ ∘ₖ physicalWaitingKernel (ρ*C)

instance dampedDensityScaledEventKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedDensityScaledEventKernel C b endTime ρ) := by
  unfold dampedDensityScaledEventKernel
  infer_instance

theorem dampedDensityScaledEvent_scale_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedDensityScaledEventKernel C b endTime (Real.toNNReal ρ) p).map (flightScaleEquiv ρ hρ.ne' x₀) =
      (dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) ∘ₖ
        physicalWaitingKernel C) (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  let e := flightScaleEquiv ρ hρ.ne' x₀
  let L := dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
  have hc : Measurable (fun q => F (e q)) := hF.comp e.measurable
  have he (q : PhysicalFlightState) :
      (∫⁻ r, F (e r) ∂dampedMediumStateCollision C b endTime q) = ∫⁻ r, F r ∂L (e q) := by
    rw [← lintegral_map hF e.measurable,dampedMediumStateCollision_scale_map C b ρ hρ.ne' t₀ endTime x₀ q]
  rw [lintegral_map hF e.measurable,dampedDensityScaledEventKernel,Kernel.lintegral_comp _ _ _ hc,
    Kernel.lintegral_comp _ _ _ hF]
  simp_rw [dampedDensityScaledCollision_lintegral C b endTime _ _ hc,he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Real.coe_toNNReal _ hρ.le]
  exact scaled_waiting_lintegral C hρ x₀ p (hF.lintegral_kernel (κ := L))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local density normalization preserves the bounded physical event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedDensityScaledEvent (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedDensityScaledEventKernel C b endTime ρ).restrict mediumVelocityBox_measurable

instance dampedBoundedDensityScaledEvent_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedBoundedDensityScaledEvent C b endTime ρ) := by
  unfold dampedBoundedDensityScaledEvent
  infer_instance

theorem dampedBoundedDensityScaledEvent_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      dampedBoundedPhysicalEvent C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  have hs : (flightScaleEquiv ρ hρ.ne' x₀) ⁻¹' mediumVelocityBox = mediumVelocityBox := rfl
  rw [dampedBoundedDensityScaledEvent,Kernel.restrict_apply,← hs,
    ← Measure.restrict_map (flightScaleEquiv ρ hρ.ne' x₀).measurable mediumVelocityBox_measurable,
    dampedDensityScaledEvent_scale_map C b hρ t₀ endTime x₀ p]
  rfl

theorem dampedBoundedDensityScaledEvent_pow_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) :
    (((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((dampedBoundedPhysicalEvent C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)))^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) :=
  kernel_pow_map (flightScaleEquiv ρ hρ.ne' x₀) _ _
    (dampedBoundedDensityScaledEvent_map C b hρ t₀ endTime x₀) n p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The bounded physical event law is a bounded characteristic collision law -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicVelocityBox : Set (ℝ × WeakTime.Phase) := {z | ‖z.2.2‖ ≤ 6}

theorem characteristicVelocityBox_measurable : MeasurableSet characteristicVelocityBox := by
  unfold characteristicVelocityBox
  exact measurableSet_le (by fun_prop) measurable_const

def dampedBoundedCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  (dampedCharacteristicKernel C b endTime).restrict characteristicVelocityBox_measurable

instance dampedBoundedCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedBoundedCharacteristicKernel C b endTime) := by
  unfold dampedBoundedCharacteristicKernel
  infer_instance

theorem dampedBoundedPhysicalEvent_transport (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    dampedBoundedPhysicalEvent C b endTime = transportedKernel (flightCharacteristicEquiv endTime)
      (dampedBoundedCharacteristicKernel C b endTime ∘ₖ WeakTime.residenceKernel C endTime) := by
  have hk : (dampedMediumStateCollision C b endTime).restrict mediumVelocityBox_measurable =
      transportedKernel (flightCharacteristicEquiv endTime)
        (dampedBoundedCharacteristicKernel C b endTime) := by
    rw [dampedBoundedCharacteristicKernel,transportedKernel_restrict,
      ← dampedStateCollision_eq_transport C b endTime]
    rfl
  unfold dampedBoundedPhysicalEvent
  rw [← Kernel.comp_restrict,hk,physicalWaitingKernel_eq_transport C endTime,
    ← transportedKernel_compKernel]

theorem dampedBoundedPhysicalEvent_pow_transport (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (n : ℕ) :
    (dampedBoundedPhysicalEvent C b endTime)^n = transportedKernel (flightCharacteristicEquiv endTime)
      ((dampedBoundedCharacteristicKernel C b endTime ∘ₖ WeakTime.residenceKernel C endTime)^n) := by
  rw [transportedKernel_pow,← dampedBoundedPhysicalEvent_transport]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The density-scaled physical histories use the same scaled characteristic clock -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def densityScaledCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  (dampedCharacteristicKernel C b endTime).withDensity (fun _ _ => ENNReal.ofReal (ρ : ℝ))

instance densityScaledCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) : IsSFiniteKernel (densityScaledCharacteristicKernel C b endTime ρ) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

def boundedDensityScaledCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) : Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  (densityScaledCharacteristicKernel C b endTime ρ).restrict characteristicVelocityBox_measurable

instance boundedDensityScaledCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (boundedDensityScaledCharacteristicKernel C b endTime ρ) := by
  unfold boundedDensityScaledCharacteristicKernel
  infer_instance

theorem dampedDensityScaledCollision_transport (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) :
    dampedDensityScaledCollision C b endTime ρ = transportedKernel (flightCharacteristicEquiv endTime)
      (densityScaledCharacteristicKernel C b endTime ρ) := by
  rw [densityScaledCharacteristicKernel,transportedKernel_constDensity]
  simp only [← dampedStateCollision_eq_transport,dampedDensityScaledCollision]

theorem dampedBoundedDensityScaledEvent_transport (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) :
    dampedBoundedDensityScaledEvent C b endTime ρ = transportedKernel (flightCharacteristicEquiv endTime)
      (boundedDensityScaledCharacteristicKernel C b endTime ρ ∘ₖ WeakTime.residenceKernel (ρ*C) endTime) := by
  have hk : (dampedDensityScaledCollision C b endTime ρ).restrict mediumVelocityBox_measurable =
      transportedKernel (flightCharacteristicEquiv endTime)
        (boundedDensityScaledCharacteristicKernel C b endTime ρ) := by
    rw [boundedDensityScaledCharacteristicKernel,transportedKernel_restrict,
      ← dampedDensityScaledCollision_transport]
    rfl
  unfold dampedBoundedDensityScaledEvent dampedDensityScaledEventKernel
  rw [← Kernel.comp_restrict,hk,physicalWaitingKernel_eq_transport (ρ*C) endTime,
    ← transportedKernel_compKernel,NNReal.coe_mul]

theorem dampedBoundedDensityScaledEvent_pow_transport (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (n : ℕ) :
    (dampedBoundedDensityScaledEvent C b endTime ρ)^n = transportedKernel (flightCharacteristicEquiv endTime)
      ((boundedDensityScaledCharacteristicKernel C b endTime ρ ∘ₖ
        WeakTime.residenceKernel (ρ*C) endTime)^n) := by
  rw [transportedKernel_pow,← dampedBoundedDensityScaledEvent_transport]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Density scaling gives the exact physical gain and loss-complement coefficients -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem densityScaledCharacteristicKernel_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) (z : ℝ × WeakTime.Phase)
    (hf : characteristicBeamFrequency b z ≤ (referenceClock : ℝ)) :
    densityScaledCharacteristicKernel C b endTime ρ z =
      ENNReal.ofReal (ρ : ℝ) • beamCharacteristicKernel b endTime z+
      ENNReal.ofReal (((ρ*C : ℝ≥0):ℝ)-(ρ:ℝ)*characteristicBeamFrequency b z) • Measure.dirac z := by
  have hm : ENNReal.ofReal (ρ : ℝ)*ENNReal.ofReal ((C:ℝ)-characteristicBeamFrequency b z) =
      ENNReal.ofReal (((ρ*C : ℝ≥0):ℝ)-(ρ:ℝ)*characteristicBeamFrequency b z) := by
    rw [← ENNReal.ofReal_mul (p := (ρ : ℝ))
      (q := (C:ℝ)-characteristicBeamFrequency b z) (show (0:ℝ) ≤ (ρ:ℝ) from ρ.property),NNReal.coe_mul]
    congr 1
    ring
  apply Measure.ext_of_lintegral
  intro f hfn
  rw [densityScaledCharacteristicKernel,Kernel.lintegral_withDensity
    (f := fun (_ : ℝ × WeakTime.Phase) (_ : ℝ × WeakTime.Phase) => ENNReal.ofReal (ρ : ℝ))
    (dampedCharacteristicKernel C b endTime) (by fun_prop) z hfn,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    dampedCharacteristicKernel_projection hC b endTime z hf,
    positiveSourceKernel_one_lintegral _ (r := fun q => (C:ℝ)-characteristicBeamFrequency b q)
      (measurable_const.sub (characteristicBeamFrequency_measurable b)) z hfn,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,lintegral_dirac,
    smul_eq_mul,smul_eq_mul,mul_add,← mul_assoc,hm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Density-scaled physical endpoint integrals in the hot trace coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaled_endpoint_characteristic (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    {f : V × V → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, clockSurvival (ρ*C) q.1*f (finishMediumFlight q)
      ∂((dampedBoundedDensityScaledEvent C b endTime ρ)^n) p) =
    ∫⁻ q, f (EuclideanFlight.flight endTime q)
      ∂(WeakTime.phaseEndpointKernel (ρ*C) endTime ∘ₖ
        ((boundedDensityScaledCharacteristicKernel C b endTime ρ ∘ₖ
          WeakTime.residenceKernel (ρ*C) endTime)^n))
        (flightCharacteristicEquiv endTime p) := by
  have hg : Measurable (fun z => f (EuclideanFlight.flight endTime z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving endTime).measurable
  have hw : Measurable (fun q : PhysicalFlightState => clockSurvival (ρ*C) q.1*f (finishMediumFlight q)) :=
    (show Measurable (fun q : PhysicalFlightState => clockSurvival (ρ*C) q.1) by
      unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)
  rw [dampedBoundedDensityScaledEvent_pow_transport,
    transportedKernel_lintegral _ _ _ hw,Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,physical_terminal_characteristic endTime (ρ*C) f]
  simp only [MeasurableEquiv.apply_symm_apply,NNReal.coe_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bounded damped endpoint measures in the coordinates of the hot trace -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedBoundedEndpoint_characteristic (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    dampedBoundedEndpointKernel C b endTime T n p =
      ((WeakTime.phaseEndpointKernel C endTime ∘ₖ
        ((dampedBoundedCharacteristicKernel C b endTime ∘ₖ WeakTime.residenceKernel C endTime)^n))
          (flightCharacteristicEquiv endTime p)).map (EuclideanFlight.flight endTime) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hg : Measurable (fun z => f (EuclideanFlight.flight endTime z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving endTime).measurable
  have hw : Measurable (fun q : PhysicalFlightState => clockSurvival C q.1*f (finishMediumFlight q)) :=
    (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)
  rw [dampedBoundedEndpointKernel_lintegral C b endTime T n p hf,
    damped_boundedMediumEventKernel_pow_eq_physical C b endTime n p hT,
    dampedBoundedPhysicalEvent_pow_transport]
  simp only [dampedMediumFlightSeed]
  rw [transportedKernel_lintegral _ _ _ hw,
    lintegral_map hf (EuclideanFlight.flight_measurePreserving endTime).measurable,
    Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,physical_terminal_characteristic endTime C f]
  simp only [MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI

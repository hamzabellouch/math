import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveContributionsIntegrable
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWaitingCone
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalCharacteristicIdentity

namespace OAI

section

/-! # Localizing the physical normal-angle source above the cold spatial cutoff -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def coldCharacteristicDomain (a η l : ℝ) : Set CharacteristicPhase :=
  {z | a ≤ z.1 ∧ 0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ ∧
    Real.exp η*l < ‖transverse (z.2.1+z.1 • z.2.2)‖}

theorem coldCharacteristicDomain_measurable (a η l : ℝ) :
    MeasurableSet (coldCharacteristicDomain a η l) := by
  have hx : Measurable (fun z : CharacteristicPhase => ‖transverse (z.2.1+z.1 • z.2.2)‖) := by
    exact ChartKernel.measurable_transverse.norm.comp (by fun_prop)
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const hx).inter (measurableSet_lt measurable_const hx))

def localizedNormalBeamKernel (b : BeamCoefficients) (ρ C a η l : ℝ)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B) :
    Kernel CharacteristicPhase CharacteristicPhase := by
  classical
  exact Kernel.piecewise (coldCharacteristicDomain_measurable a η l)
    ((beamNormalRetainedKernel b ρ C).restrict hB) 0

instance localizedNormalBeamKernel_sFinite (b : BeamCoefficients) (ρ C a η l : ℝ)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B) :
    IsSFiniteKernel (localizedNormalBeamKernel b ρ C a η l hB) := by
  unfold localizedNormalBeamKernel
  infer_instance

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The localized normal-angle collision law in physical flight coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedNormalCollision (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  transportedKernel (flightCharacteristicEquiv T)
    (localizedNormalBeamKernel b ρ C a η l hΩ)

instance localizedNormalCollision_sFinite (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalCollision b ρ C T a η l hΩ) := by
  unfold localizedNormalCollision
  infer_instance

theorem localizedNormalCollision_eq_restrict {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (p : PhysicalFlightState)
    (hz : flightCharacteristicEquiv T p ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hf : characteristicBeamFrequency b (flightCharacteristicEquiv T p) ≤ (referenceClock:ℝ)) :
    localizedNormalCollision b ρ (ρ*C) T a η l hΩ p =
      (dampedDensityScaledCollision C b T ρ p).restrict ((flightCharacteristicEquiv T) ⁻¹' Ω) := by
  classical
  apply Measure.ext_of_lintegral
  intro f hfn
  let e := flightCharacteristicEquiv T
  rw [localizedNormalCollision,transportedKernel_lintegral _ _ p hfn,
    localizedNormalBeamKernel,Kernel.piecewise_apply,ite_eq_left hz,Kernel.restrict_apply,
    beamNormalRetainedKernel_eq_scaled hC b T ρ (e p) hp hm hf]
  have he := congrArg (fun K : Kernel PhysicalFlightState PhysicalFlightState => K p)
    (transportedKernel_restrict e (densityScaledCharacteristicKernel C b T ρ) hΩ)
  rw [← dampedDensityScaledCollision_transport] at he
  change (∫⁻ y in Ω, f (e.symm y) ∂densityScaledCharacteristicKernel C b T ρ (e p)) =
    ∫⁻ x, f x ∂((dampedDensityScaledCollision C b T ρ).restrict (e.measurable hΩ)) p
  rw [← he,transportedKernel_lintegral _ _ p hfn]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local measure balances with one fixed phase cutoff -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def phaseWeight (β : Phase → ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ := β z.2*F z

def weightedPhaseSource (μ : Measure (ℝ × Phase)) (β : Phase → ℝ) : Measure (ℝ × Phase) :=
  positiveDensityMeasure μ (fun z => β z.2)

theorem phaseWeight_integrable {β : Phase → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) {F : ℝ × Phase → ℝ} (hi : Integrable F) :
    Integrable (phaseWeight β F) := by
  obtain ⟨C,hC⟩ := hβ.bounded_above_of_compact_support hc
  exact hi.bdd_mul (hβ.measurable.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hC z.2))

theorem weightedPhaseSource_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {β : Phase → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hn : ∀ p, 0 ≤ β p) :
    IsFiniteMeasure (weightedPhaseSource μ β) := by
  obtain ⟨C,hC⟩ := hβ.bounded_above_of_compact_support hc
  apply positiveDensityMeasure_finite
  · exact (integrable_const C).mono' (hβ.measurable.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.2))
  · exact ae_of_all _ (fun z => hn z.2)

theorem ae_localized_measure_interval_balance {a b : ℝ} (hab : a < b)
    {F : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (μ ν : Measure (ℝ × Phase)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {β : Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → tsupport φ ⊆ tsupport β →
      ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, θ z.1*φ z.2 ∂ν) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice (phaseWeight β F) t+phaseIncrement (weightedPhaseSource ν β) s t =
      phaseSlice (phaseWeight β F) s+phaseIncrement (weightedPhaseSource μ β) s t := by
  let _ := weightedPhaseSource_finite μ hβ.continuous hβc hβn
  let _ := weightedPhaseSource_finite ν hβ.continuous hβc hβn
  apply ae_measure_interval_balance hab (phaseWeight_integrable hβ.continuous hβc hi)
    (hn.mono (fun z hz => mul_nonneg (hβn z.2) hz))
  intro φ hφ _hφc hφn θ hθ hθc hθs
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun p => φ p*β p) := hφ.mul hβ
  have hp := hw (fun p => φ p*β p) hprod hβc.mul_left
    (fun p => mul_nonneg (hφn p) (hβn p)) tsupport_mul_subset_right θ hθ hθc hθs
  have hβmμ : AEMeasurable (fun z : ℝ × Phase => β z.2) μ := by
    simpa only [Function.comp_def] using
      (hβ.continuous.measurable.comp measurable_snd).aemeasurable (μ := μ)
  have hβmν : AEMeasurable (fun z : ℝ × Phase => β z.2) ν := by
    simpa only [Function.comp_def] using
      (hβ.continuous.measurable.comp measurable_snd).aemeasurable (μ := ν)
  rw [show weightedPhaseSource μ β = positiveDensityMeasure μ (fun z => β z.2) from rfl,
    show weightedPhaseSource ν β = positiveDensityMeasure ν (fun z => β z.2) from rfl,
    positiveDensityMeasure_integral hβmμ (ae_of_all _ (fun z => hβn z.2)),
    positiveDensityMeasure_integral hβmν (ae_of_all _ (fun z => hβn z.2))]
  simpa only [phaseWeight,mul_assoc] using hp

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Finite bounded physical histories are dominated by the localized actual angular histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedNormalPhysicalEvent (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  localizedNormalCollision b ρ C T a η l hΩ ∘ₖ physicalWaitingKernel (Real.toNNReal C)

instance localizedNormalPhysicalEvent_sFinite (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalPhysicalEvent b ρ C T a η l hΩ) := by
  unfold localizedNormalPhysicalEvent
  infer_instance

theorem boundedCollision_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {p q : PhysicalFlightState} (hq : boundedFlightCone p q)
    (hΩcone : ∀ r, boundedFlightCone p r → flightCharacteristicEquiv T r ∈ Ω)
    (hz : flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    (hf : characteristicBeamFrequency b (flightCharacteristicEquiv T q) ≤ (referenceClock:ℝ)) :
    (dampedDensityScaledCollision C b T ρ q).restrict mediumVelocityBox ≤
      localizedNormalCollision b ρ (ρ*C) T a η l hΩ q := by
  rw [localizedNormalCollision_eq_restrict hC b ρ T a η l hΩ q hz hp hm hf]
  apply Measure.restrict_mono_ae
  filter_upwards [dampedDensityScaledCollision_ae_fixed C b T ρ q] with r hr
  intro hv
  apply hΩcone r
  exact ⟨hr.1 ▸ hq.1,hr.1 ▸ hq.2.1,hv,by rw [hr.1,hr.2]; exact hq.2.2.2⟩

theorem boundedHistory_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
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
      ((localizedNormalPhysicalEvent b ρ (ρ*C) T a η l hΩ)^n) p := by
  apply kernel_pow_le_on_invariant _ _ {q | boundedFlightCone p q} _ _ n p
    (boundedFlightCone_refl ht hv)
  · intro q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b T ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr
  · intro q hq
    unfold dampedBoundedDensityScaledEvent dampedDensityScaledEventKernel localizedNormalPhysicalEvent
    rw [← Kernel.comp_restrict,← NNReal.coe_mul,Real.toNNReal_coe]
    apply KernelHistoryOrder.measure_comp_mono_ae (hμ := le_rfl)
    filter_upwards [physicalWaitingKernel_ae_cone (ρ*C) q hq.2.2.1] with r hr
    have hpr := boundedFlightCone_trans hq hr
    obtain ⟨hz,hp,hm,hf⟩ := hlocal r hpr
    exact boundedCollision_le_localized hC b ρ T a η l hΩ hpr hΩcone hz hp hm hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Constant damping for weak evolution localized in characteristic phase -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_localized_damped_measure_balance {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {F L : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hL : Integrable L (volume : Measure (ℝ × Phase))) (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {β : Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hbound : ∀ᵐ z ∂volume, z.1 ∈ Ioo a b → β z.2*L z ≤ C*(β z.2*F z))
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → tsupport φ ⊆ tsupport β →
      ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, (θ z.1*φ z.2)*L z) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice (timeWeightedDensity a b C (phaseWeight β F)) t =
        phaseSlice (timeWeightedDensity a b C (phaseWeight β F)) s+
          phaseIncrement (timeWeightedSource a b C (weightedPhaseSource μ β)+
            positiveDensityMeasure volume
              (dampedResidual a b C (phaseWeight β F) (phaseWeight β L))) s t := by
  let _ := weightedPhaseSource_finite μ hβ.continuous hβc hβn
  apply ae_damped_measure_interval_balance hab hC
    (phaseWeight_integrable hβ.continuous hβc hi)
    (phaseWeight_integrable hβ.continuous hβc hL)
    (hn.mono (fun z hz => mul_nonneg (hβn z.2) hz)) hbound
  intro φ hφ _hc hφn θ hθ hθc hθs
  have hp := hw (fun p => φ p*β p) (hφ.mul hβ) hβc.mul_left
    (fun p => mul_nonneg (hφn p) (hβn p)) tsupport_mul_subset_right θ hθ hθc hθs
  have hβm : AEMeasurable (fun z : ℝ × Phase => β z.2) μ := by
    simpa only [Function.comp_def] using
      (hβ.continuous.measurable.comp measurable_snd).aemeasurable (μ := μ)
  rw [show weightedPhaseSource μ β = positiveDensityMeasure μ (fun z => β z.2) from rfl,
    positiveDensityMeasure_integral hβm (ae_of_all _ (fun z => hβn z.2))]
  simpa only [phaseWeight,mul_assoc] using hp

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI

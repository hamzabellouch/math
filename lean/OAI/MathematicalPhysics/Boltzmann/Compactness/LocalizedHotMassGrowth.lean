import OAI.MathematicalPhysics.Boltzmann.Branching.EndpointHistoryMass
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSliceLocalization
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedBlockComparison
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricLocalizedEntry

namespace OAI

section

/-! # Converting finite angular blocks to growth of a dominated hot measure -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

 theorem localizedHistoryBlockMass_eq_measure (b : BeamCoefficients)
    (ρ C T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {A : Set (V × V)} (hA : MeasurableSet A) (N : ℕ) (z : ℝ × WeakTime.Phase) :
    localizedHistoryBlockMass b ρ C T a η l s hΩ A N z =
      (WeakTime.phaseEndpointKernel C T ∘ₖ
        ∑ n ∈ Finset.range N,
          ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
            (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
              WeakTime.residenceKernel C T)^n)) z (EuclideanFlight.flight T ⁻¹' A) := by
  let f : WeakTime.Phase → ℝ≥0∞ := (EuclideanFlight.flight T ⁻¹' A).indicator 1
  have hf : Measurable f := measurable_const.indicator
    (hA.preimage (EuclideanFlight.flight_measurePreserving T).measurable)
  rw [← lintegral_indicator_one
    (hA.preimage (EuclideanFlight.flight_measurePreserving T).measurable)]
  rw [kernel_lintegral_comp_finset _ _ _ _ hf]
  rfl

theorem localized_history_mass_growth (b : BeamCoefficients)
    (ρ C T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {A B : Set WeakTime.Phase} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (N : ℕ) (g : ℝ≥0∞) (μ ν : Measure WeakTime.Phase)
    (hdom : WeakTime.phaseEndpointKernel C T ∘ₘ
      (∑ n ∈ Finset.range N,
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T)^n) :
          Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase)) ∘ₘ WeakTime.phaseSeed s μ ≤ ν)
    (hblock : ∀ p ∈ B, g ≤ localizedHistoryBlockMass b ρ C T a η l s hΩ A N (s,p)) :
    g*μ B ≤ ν (EuclideanFlight.flight T ⁻¹' A) := by
  rw [Measure.comp_assoc] at hdom
  exact endpoint_mass_of_pointwise _ μ ν s
    (hA.preimage (EuclideanFlight.flight_measurePreserving T).measurable) hB g hdom
    (fun p hp => (localizedHistoryBlockMass_eq_measure b ρ C T a η l s hΩ hA N (s,p)) ▸
      hblock p hp)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Localized normal-angle histories use one kernel for every density scale -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem localizedNormalBeamKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η C a l : ℝ)
    {B : Set EuclideanFlight.CharacteristicPhase} (hB : MeasurableSet B) :
    localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) C a η l hB =
      localizedNormalBeamKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) C a η l hB := by
  classical
  exact congrArg (fun Q : Kernel EuclideanFlight.CharacteristicPhase EuclideanFlight.CharacteristicPhase =>
    Kernel.piecewise (coldCharacteristicDomain_measurable a η l) (Q.restrict hB) 0)
    (beamNormalRetainedKernel_independent hθ hK hα hγ hr hs η C)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The finite physical endpoint mass does not depend on its reference density scale -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem localizedHistoryBlockMass_independent {θ K α γ r r' : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hr' : 0 < r') (η C T a l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (A : Set WeakTime.Phase) (N : ℕ) (z : ℝ × WeakTime.Phase) :
    localizedHistoryBlockMass (beamCoefficients hθ hα hγ η r) (K/(4*r)) C T a η l s hΩ A N z =
      localizedHistoryBlockMass (beamCoefficients hθ hα hγ η r') (K/(4*r')) C T a η l s hΩ A N z := by
  unfold localizedHistoryBlockMass
  rw [localizedNormalBeamKernel_independent hθ hK hα hγ hr hr' η C a l hΩ]

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Passing a covered finite-history lower bound to the actual hot box mass -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localized_hot_mass_growth (b : BeamCoefficients) (ρ C t a A R η l s κ d : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ} (hf : ∀ z, 0 ≤ f z)
    {β : WeakTime.Phase → ℝ} (hβ₁ : ∀ p, β p ≤ 1)
    (hcover : ∀ p ∈ tsupport β,
      hotCharacteristicEquiv (s,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R)
    (hcore : ∀ p ∈ flight s ⁻¹' lateBox κ d s, β p = 1)
    (N : ℕ) (g : ℝ≥0∞)
    (hdom : WeakTime.phaseEndpointKernel C t ∘ₘ
      (∑ n ∈ Finset.range N,
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
            WeakTime.residenceKernel C t)^n)) ∘ₘ
      WeakTime.phaseSeed s (WeakTime.phaseSlice
        (WeakTime.phaseWeight β (cylinderPullback a A R f)) s) ≤
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t)
    (hpoint : ∀ p ∈ flight s ⁻¹' lateBox κ d s,
      g ≤ localizedHistoryBlockMass b ρ C t a η l s hΩ (lateBox κ d t) N (s,p)) :
    g*hotLateBoxMass f κ d s ≤ hotLateBoxMass f κ d t := by
  let μ := WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) s
  let ν := WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t
  have hBs := (lateBox_measurable κ d s).preimage (flight_measurePreserving s).measurable
  have heq := cylinder_phaseSlice_eq_on (f := f) hBs hcore hcover
  have hm : g*μ (flight s ⁻¹' lateBox κ d s) ≤ ν (flight t ⁻¹' lateBox κ d t) := by
    apply localized_history_mass_growth b ρ C t a η l s hΩ
      (lateBox_measurable κ d t) hBs N g μ ν
    · simpa only [FunLike.coe_sum] using hdom
    · exact hpoint
  calc
    g*hotLateBoxMass f κ d s = g*μ (flight s ⁻¹' lateBox κ d s) :=
      congrArg (fun x : ℝ≥0∞ => g*x) heq.symm
    _ ≤ ν (flight t ⁻¹' lateBox κ d t) := hm
    _ ≤ hotLateBoxMass f κ d t := cylinder_phaseSlice_le hf hβ₁ a A R t _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI

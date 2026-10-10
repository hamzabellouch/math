import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedHotMassGrowth
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantOrder

namespace OAI

/-! # Time-pair growth from covered endpoint-history domination -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem ae_localized_hot_mass_growth (b : BeamCoefficients) (ρ C a A η l κ d : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ} (hf : ∀ z, 0 ≤ f z)
    {β : WeakTime.Phase → ℝ} (hβ₁ : ∀ p, β p ≤ 1)
    (N : ℕ) (g : ℝ≥0∞) (P : ℝ → ℝ → Prop)
    (hhist : ∃ R : ℝ, 0 ≤ R ∧
      (∀ s ∈ Icc a A, ∀ p ∈ tsupport β,
        hotCharacteristicEquiv (s,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
        WeakTime.phaseEndpointKernel C t ∘ₘ
          (∑ j ∈ Finset.range n,
            ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
              (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
                WeakTime.residenceKernel C t)^j) ∘ₘ
          WeakTime.phaseSeed s (WeakTime.phaseSlice
            (WeakTime.phaseWeight β (cylinderPullback a A R f)) s)) ≤
          WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t)
    (hstart : ∀ s ∈ Ioo a A, ∀ p ∈ flight s ⁻¹' lateBox κ d s, β p = 1)
    (horder : ∀ s ∈ Ioo a A, ∀ t ∈ Ioo a A, P s t → s ≤ t)
    (hblock : ∀ s ∈ Ioo a A, ∀ t ∈ Ioo a A, P s t →
      ∀ p ∈ flight s ⁻¹' lateBox κ d s, g ≤ localizedHistoryBlockMass
        b ρ C t a η l s hΩ (lateBox κ d t) N (s,p)) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a A → t ∈ Ioo a A → P s t →
      g*hotLateBoxMass f κ d s ≤ hotLateBoxMass f κ d t := by
  obtain ⟨R,_hR,hcover,hist⟩ := hhist
  filter_upwards [hist] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hp
  have hh := ht hsa hta (horder s hsa t hta hp) N
  rw [← kernel_finset_comp_measure] at hh
  apply localized_hot_mass_growth b ρ C t a A R η l s κ d hΩ hf hβ₁
    (hcover s ⟨hsa.1.le,hsa.2.le⟩) (hstart s hsa) N g
  · simpa only [FunLike.coe_sum] using hh
  · exact hblock s hsa t hta hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI

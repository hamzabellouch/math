import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicPhysicalGain
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure

namespace OAI

/-! # Removing phase and spatial cutoffs from the masses in a covered box -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotPhaseSlice (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ) (t : ℝ) :
    Measure WeakTime.Phase :=
  positiveDensityMeasure volume (fun p => f (hotCharacteristicEquiv (t,p)))

def hotLateBoxMass (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ)
    (κ d t : ℝ) : ℝ≥0∞ :=
  hotPhaseSlice f t (flight t ⁻¹' ReferenceGeometry.lateBox κ d t)

theorem cylinder_phaseSlice_le {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : ∀ z, 0 ≤ f z) {β : WeakTime.Phase → ℝ}
    (hβ₁ : ∀ p, β p ≤ 1) (a A R t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t ≤ hotPhaseSlice f t := by
  apply withDensity_mono
  apply ae_of_all
  intro p
  apply ENNReal.ofReal_le_ofReal
  change β p*(JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R).indicator f
    (hotCharacteristicEquiv (t,p)) ≤ f (hotCharacteristicEquiv (t,p))
  by_cases hp : hotCharacteristicEquiv (t,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R
  · rw [indicator_of_mem hp]
    exact (mul_le_mul_of_nonneg_right (hβ₁ p) (hf _)).trans_eq (one_mul _)
  · rw [indicator_of_notMem hp,mul_zero]
    exact hf _

theorem cylinder_phaseSlice_eq_on {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    {β : WeakTime.Phase → ℝ} {a A R t : ℝ} {B : Set WeakTime.Phase}
    (hB : MeasurableSet B) (hβ : ∀ p ∈ B, β p = 1)
    (hcover : ∀ p ∈ tsupport β,
      hotCharacteristicEquiv (t,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t B =
      hotPhaseSlice f t B := by
  unfold WeakTime.phaseSlice hotPhaseSlice positiveDensityMeasure
  rw [withDensity_apply _ hB,withDensity_apply _ hB]
  apply setLIntegral_congr_fun hB
  intro p hp
  have hc := hcover p (subset_tsupport β (show β p ≠ 0 by rw [hβ p hp]; norm_num))
  simp only [WeakTime.phaseWeight,cylinderPullback,Function.comp_apply,
    indicator_of_mem hc,hβ p hp,one_mul]

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI

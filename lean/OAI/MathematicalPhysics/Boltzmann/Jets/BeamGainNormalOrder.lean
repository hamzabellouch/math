import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance

namespace OAI

/-! # The physical gain law lies below the localized positive normal-angle source -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamCharacteristic_le_retained (b : BeamCoefficients) (T C : ℝ)
    (z : CharacteristicPhase)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z)) :
    beamCharacteristicKernel b T z ≤ beamNormalRetainedKernel b 1 C z := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : CharacteristicPhase → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [← lintegral_indicator_one hA,← lintegral_indicator_one hA,
    beamNormalRetainedKernel_lintegral b 1 C z hf,
    beamNormalCharacteristicKernel_eq b T z hp hm,ENNReal.ofReal_one,one_mul]
  exact le_add_of_nonneg_right bot_le

theorem physicalBeamCollision_le_localized (b : BeamCoefficients) (T C a η l : ℝ)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (p : PhysicalFlightState)
    (hz : flightCharacteristicEquiv T p ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (houtput : ∀ᵐ q ∂physicalBeamCollision b T p, flightCharacteristicEquiv T q ∈ Ω) :
    physicalBeamCollision b T p ≤ localizedNormalCollision b 1 C T a η l hΩ p := by
  classical
  let e := flightCharacteristicEquiv T
  have he : transportedKernel e (beamCharacteristicKernel b T) = physicalBeamCollision b T := by
    unfold beamCharacteristicKernel
    exact transportedKernel_symm e _
  have hre : (physicalBeamCollision b T p).restrict (e ⁻¹' Ω) = physicalBeamCollision b T p :=
    Measure.restrict_eq_self_of_ae_mem houtput
  have hrestricted : (transportedKernel e ((beamCharacteristicKernel b T).restrict hΩ)) p =
      physicalBeamCollision b T p := by
    rw [transportedKernel_restrict,he,Kernel.restrict_apply,hre]
  rw [← hrestricted]
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [← lintegral_indicator_one hA,← lintegral_indicator_one hA,
    transportedKernel_lintegral e _ p hf,localizedNormalCollision,
    transportedKernel_lintegral e _ p hf]
  rw [localizedNormalBeamKernel,Kernel.piecewise_apply,ite_eq_left hz]
  apply lintegral_mono'
  · exact Measure.restrict_mono subset_rfl (beamCharacteristic_le_retained b T C (e p) hp hm)
  · exact le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI

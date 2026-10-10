import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBoundedEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing

namespace OAI

section

/-! # A density-scaled normal-angle beam source with its exact loss complement -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def scaledBeamNormalKernel (b : BeamCoefficients) (ρ : ℝ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  (beamNormalCharacteristicKernel b).withDensity (fun _ _ => ENNReal.ofReal ρ)

instance scaledBeamNormalKernel_sFinite (b : BeamCoefficients) (ρ : ℝ) :
    IsSFiniteKernel (scaledBeamNormalKernel b ρ) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem scaledBeamNormalKernel_apply (b : BeamCoefficients) (ρ : ℝ) (z : CharacteristicPhase) :
    scaledBeamNormalKernel b ρ z = ENNReal.ofReal ρ • beamNormalCharacteristicKernel b z := by
  rw [scaledBeamNormalKernel,Kernel.withDensity_apply _ (by fun_prop),withDensity_const]

def beamNormalRetainedKernel (b : BeamCoefficients) (ρ C : ℝ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  positiveSourceKernel (scaledBeamNormalKernel b ρ) (fun _ => 1)
    (fun z => C-ρ*characteristicBeamFrequency b z)

instance beamNormalRetainedKernel_sFinite (b : BeamCoefficients) (ρ C : ℝ) :
    IsSFiniteKernel (beamNormalRetainedKernel b ρ C) := by
  unfold beamNormalRetainedKernel
  infer_instance

theorem beamNormalRetainedKernel_lintegral (b : BeamCoefficients) (ρ C : ℝ)
    (z : CharacteristicPhase) {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂beamNormalRetainedKernel b ρ C z) =
      ENNReal.ofReal ρ*(∫⁻ y, f y ∂beamNormalCharacteristicKernel b z)+
        ENNReal.ofReal (C-ρ*characteristicBeamFrequency b z)*f z := by
  rw [beamNormalRetainedKernel,positiveSourceKernel_one_lintegral _
    (r := fun z => C-ρ*characteristicBeamFrequency b z)
    (measurable_const.sub (measurable_const.mul (characteristicBeamFrequency_measurable b))) z hf,
    scaledBeamNormalKernel_apply,lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact identification of physical angular histories in characteristic coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamNormalCharacteristicKernel_eq (b : BeamCoefficients) (endTime : ℝ)
    (z : CharacteristicPhase) (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z)) :
    beamNormalCharacteristicKernel b z = beamCharacteristicKernel b endTime z := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hj : Measurable (fun v => f (characteristicBeamJump z v)) := by
    apply hf.comp
    unfold characteristicBeamJump
    fun_prop
  rw [beamNormalCharacteristicKernel_lintegral b z hf,
    normalGain_beam_projection b (characteristicBeamPoint z) z.2.2 hp hm,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,
    smul_eq_mul,outgoing_lintegral _ _ hj,outgoing_lintegral _ _ hj,
    beamCharacteristicKernel_lintegral b endTime z hf]
  unfold mediumMarkedRate markedRate markedChild
  norm_num
  rw [sphereProbability,lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul]
  simp only [mul_assoc]
  simp only [ENNReal.ofReal_mul (p := (4:ℝ)) (q := Real.pi) (by norm_num),
    ENNReal.ofReal_ofNat]

theorem beamNormalRetainedKernel_eq_scaled {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) (z : CharacteristicPhase)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z))
    (hf : characteristicBeamFrequency b z ≤ (referenceClock:ℝ)) :
    beamNormalRetainedKernel b ρ (ρ*C) z = densityScaledCharacteristicKernel C b endTime ρ z := by
  rw [densityScaledCharacteristicKernel_projection hC b endTime ρ z hf]
  apply Measure.ext_of_lintegral
  intro f hfn
  rw [beamNormalRetainedKernel_lintegral b ρ (ρ*C) z hfn,
    beamNormalCharacteristicKernel_eq b endTime z hp hm,lintegral_add_measure,
    lintegral_smul_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul,smul_eq_mul]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI

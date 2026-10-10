import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeCompletedAdjoint
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeWeakLift

namespace OAI

/-! The actual cubed-prime correspondence preserves the full global
weak spectral equation, by its common mass and energy adjoint. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeEnergyPencil_pairing {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaEnergyPencil z (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaPrimeCubeHeckeAdjoint hp u) (cubicThetaEnergyPencil z v) := by
  rw [cubicThetaGlobalEnergyPencil_pairing,cubicThetaGlobalEnergyPencil_pairing,
    cubicThetaPrimeCubeHeckeEnergy_adjoint,cubicThetaPrimeCubeHeckeEnergy_mass_adjoint]

theorem cubicThetaPrimeCubeHeckeEnergy_kernel {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (v : cubicThetaGlobalEnergySpace) (hv : cubicThetaEnergyPencil z v=0) :
    cubicThetaEnergyPencil z (cubicThetaPrimeCubeHeckeEnergy hp v)=0 := by
  apply ext_inner_left ℂ
  intro u
  rw [cubicThetaPrimeCubeEnergyPencil_pairing,hv,inner_zero_right,inner_zero_right]

end CubicFirstMoment

end

end OAI

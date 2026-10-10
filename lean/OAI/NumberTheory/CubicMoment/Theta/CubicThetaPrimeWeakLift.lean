import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTracePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinEnergyInvolution
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeakUniqueness

namespace OAI

/-! The actual finite-cover trace transports the complete weak energy
equation to the prime cover, with all finite-cover test vectors allowed. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeEnergyPencil {p : Eisenstein} (hp : primaryPrime p) (z : ℂ) :
    cubicThetaPrimeEnergySpace hp →L[ℂ] cubicThetaPrimeEnergySpace hp :=
  1-z • ((cubicThetaPrimeEnergyInclusion hp).adjoint.comp (cubicThetaPrimeEnergyInclusion hp))

lemma cubicThetaPrimeEnergyPencil_pairing {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (u v : cubicThetaPrimeEnergySpace hp) :
    inner ℂ u (cubicThetaPrimeEnergyPencil hp z v)=inner ℂ u v-
      z*inner ℂ (cubicThetaPrimeEnergyInclusion hp u) (cubicThetaPrimeEnergyInclusion hp v) := by
  change inner ℂ u (v-z • (cubicThetaPrimeEnergyInclusion hp).adjoint
    (cubicThetaPrimeEnergyInclusion hp v))=_
  rw [inner_sub_right,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeEnergySpace hp),
    (cubicThetaPrimeEnergyInclusion hp).adjoint_inner_right]

lemma cubicThetaGlobalEnergyPencil_pairing (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaEnergyPencil z v)=inner ℂ u v-
      z*inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v) := by
  change inner ℂ u (v-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion v))=_
  rw [inner_sub_right,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace),
    cubicThetaGlobalInclusion.adjoint_inner_right]

theorem cubicThetaPrimeEnergyPencil_lift_pairing {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (u : cubicThetaPrimeEnergySpace hp) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaPrimeEnergyPencil hp z (cubicThetaPrimeLiftEnergy hp v))=
      inner ℂ (cubicThetaPrimeTraceEnergy hp u) (cubicThetaEnergyPencil z v) := by
  rw [cubicThetaPrimeEnergyPencil_pairing,cubicThetaGlobalEnergyPencil_pairing,
    cubicThetaPrimeTraceEnergy_pairing,cubicThetaPrimeTraceEnergy_mass_pairing]

theorem cubicThetaPrimeEnergyPencil_lift_kernel {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (v : cubicThetaGlobalEnergySpace) (hv : cubicThetaEnergyPencil z v=0) :
    cubicThetaPrimeEnergyPencil hp z (cubicThetaPrimeLiftEnergy hp v)=0 := by
  apply ext_inner_left ℂ
  intro u
  rw [cubicThetaPrimeEnergyPencil_lift_pairing,hv,inner_zero_right,inner_zero_right]

lemma cubicThetaPrimeEnergyPencil_atkin_pairing {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (u v : cubicThetaPrimeEnergySpace hp) :
    inner ℂ (cubicThetaPrimeAtkinEnergy hp u)
      (cubicThetaPrimeEnergyPencil hp z (cubicThetaPrimeAtkinEnergy hp v))=
        inner ℂ u (cubicThetaPrimeEnergyPencil hp z v) := by
  rw [cubicThetaPrimeEnergyPencil_pairing,cubicThetaPrimeEnergyPencil_pairing,
    (cubicThetaPrimeAtkinEnergy hp).inner_map_map,cubicThetaPrimeAtkinEnergy_mass_inner]

theorem cubicThetaPrimeEnergyPencil_atkin_kernel {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (v : cubicThetaPrimeEnergySpace hp) (hv : cubicThetaPrimeEnergyPencil hp z v=0) :
    cubicThetaPrimeEnergyPencil hp z (cubicThetaPrimeAtkinEnergy hp v)=0 := by
  apply ext_inner_left ℂ
  intro u
  have he := cubicThetaPrimeEnergyPencil_atkin_pairing hp z (cubicThetaPrimeAtkinEnergy hp u) v
  rw [cubicThetaPrimeAtkinEnergy_involutive,hv,inner_zero_right] at he
  exact he.trans (inner_zero_right u).symm

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionMass

namespace OAI

/-! The exact local Weyl row for every vector in the actual global mass completion. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_mass_formula {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootWeylL2 hp
      (cubicThetaPrimeRootFourierL2 hp k (cubicThetaPrimeRootLiftL2 hp u)))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFourierL2 hp j
          (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))+
          (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
            cubicThetaPrimeRootFourierL2 hp j
              (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass u))) := by
  let L : cubicThetaAutomorphicL2 →L[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
    (cubicThetaPrimeRootFourierL2 hp j).comp
      ((cubicThetaPrimeRootWeylL2 hp).toContinuousLinearMap.comp
        ((cubicThetaPrimeRootFourierL2 hp k).comp (cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap))
  let R : cubicThetaAutomorphicL2 →L[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
    (norm p:ℂ)⁻¹ •
      ((cubicThetaPrimeRootFourierL2 hp j).comp
        ((cubicThetaPrimeRootWeylL2 hp).toContinuousLinearMap.comp (cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap)+
      (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
        (cubicThetaPrimeRootFourierL2 hp j).comp
          ((cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap.comp (cubicThetaInversionMass.toContinuousLinearMap)))
  change L u=R u
  refine cubicThetaGlobalMassClosure_dense.induction_on u (isClosed_eq L.continuous R.continuous) ?_
  intro F
  change cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootWeylL2 hp
    (cubicThetaPrimeRootFourierL2 hp k (cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F))))=
      (norm p:ℂ)⁻¹ •
        (cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootWeylL2 hp
          (cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F)))+
        (cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp j k) •
          cubicThetaPrimeRootFourierL2 hp j (cubicThetaPrimeRootLiftL2 hp
            (cubicThetaInversionMass (cubicThetaGlobalMassClosure F))))
  rw [cubicThetaInversionMass_smooth]
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [cubicThetaPrimeRootWeylL2_smooth_formula hp j k F]
  module

end CubicFirstMoment

end

end OAI

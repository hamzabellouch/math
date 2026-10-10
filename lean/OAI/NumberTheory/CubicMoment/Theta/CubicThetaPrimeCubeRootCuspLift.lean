import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootLiftL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRestriction

namespace OAI

/-! Compatibility of the actual cubic-root restriction with the original
energy-space cusp observation. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteCuspRestriction hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)=
      cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F) := by
  exact MemLp.toLp_congr
    (cubicThetaPrimeCubeRoot_strip_memLp hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))
    (cubicThetaFiniteEnergy_strip_memLp (cubicThetaSmoothToFiniteEnergy F))
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem cubicThetaPrimeCubeRootCuspRestriction_lift {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootCuspRestriction hp
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
        cubicThetaCuspRestriction u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootCuspRestriction hp).continuous.comp
      ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp cubicThetaGlobalEnergyValueMap.continuous))
      ((continuous_const (y:=((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))).smul
        cubicThetaCuspRestriction.continuous)) ?_
  intro F
  change cubicThetaPrimeCubeRootCuspRestriction hp
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)))=_
  rw [cubicThetaGlobalEnergyValueMap_test,cubicThetaPrimeCubeRootLiftL2_smooth]
  change cubicThetaPrimeCubeRootCuspRestriction hp
    (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))=_
  rw [map_smul,cubicThetaPrimeCubeRootCuspRestriction_finite,
    cubicThetaPrimeCubeRootFiniteCuspRestriction_smooth]
  congr 1
  change cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F)=
    cubicThetaCuspRestriction (cubicThetaGlobalEnergyTest F)
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]

end CubicFirstMoment

end

end OAI

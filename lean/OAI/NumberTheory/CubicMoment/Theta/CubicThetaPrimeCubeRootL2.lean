import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootMassTransport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootResidues
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm

namespace OAI

/-! Square-integrable cubic-root sections on the actual finite domain.
The finite translation action has exactly the original L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaPrimeCubeRootL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))

def cubicThetaPrimeCubeRootFiniteSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeCubeRootSections p) where
  carrier := {F | MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

def cubicThetaPrimeCubeRootFiniteValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] CubicThetaPrimeCubeRootL2 hp where
  toFun F := F.property.toLp _
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

lemma cubicThetaPrimeCubeRootSectionL2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteValue hp F‖^2=
      ∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  change ‖F.property.toLp F.val.val‖^2=_
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp] with x hx
  rw [hx]

def cubicThetaPrimeCubeRootFiniteTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootSectionTranslate hp x F.val,
    cubicThetaPrimeCubeRootSectionTranslate_memLp hp x F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootFiniteTranslate_norm {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootFiniteTranslate hp x F)‖=
      ‖cubicThetaPrimeCubeRootFiniteValue hp F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq,cubicThetaPrimeCubeRootSectionL2_norm_sq]
  exact cubicThetaPrimeCubeRootSectionTranslate_mass hp x F.val

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverBorel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm

namespace OAI

/-! Actual L2 representatives of sections on the finite root cover.
The Weyl action preserves square integrability and the exact L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaPrimeRootL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp ℂ 2 (cubicThetaPrimeRootCoverMeasure hp)

def cubicThetaPrimeRootSectionRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) : ℂ :=
  F.val (cubicThetaPrimeRootBorelSection hp q)

lemma cubicThetaPrimeRootSectionRepresentative_measurable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : Measurable (cubicThetaPrimeRootSectionRepresentative hp F) :=
  F.val.continuous.measurable.comp (cubicThetaPrimeRootBorelSection_measurable hp)

lemma cubicThetaPrimeRootSectionRepresentative_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    ‖cubicThetaPrimeRootSectionRepresentative hp F q‖=cubicThetaPrimeRootSectionNorm hp F q := by
  have he := cubicThetaPrimeRootSectionNorm_apply hp F (cubicThetaPrimeRootBorelSection hp q)
  rw [cubicThetaPrimeRootBorelSection_rightInverse hp q] at he
  exact he.symm

lemma cubicThetaPrimeRootWeylSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    MemLp (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootWeylSection hp F))
      2 (cubicThetaPrimeRootCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeRootSectionRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving (cubicThetaPrimeRootCoverWeyl_measurePreserving hp)
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootWeylSection_norm] using hc

lemma cubicThetaPrimeRootSectionL2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    ‖hF.toLp (cubicThetaPrimeRootSectionRepresentative hp F)‖^2=
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with q hq
  rw [hq,cubicThetaPrimeRootSectionRepresentative_norm]

lemma cubicThetaPrimeRootWeylSection_L2_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    ‖(cubicThetaPrimeRootWeylSection_memLp hp F hF).toLp
      (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootWeylSection hp F))‖=
      ‖hF.toLp (cubicThetaPrimeRootSectionRepresentative hp F)‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeRootSectionL2_norm_sq,cubicThetaPrimeRootSectionL2_norm_sq]
  exact cubicThetaPrimeRootWeylSection_mass hp F

def cubicThetaPrimeRootFiniteSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeRootSections p) where
  carrier := {F | MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

def cubicThetaPrimeRootFiniteValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] CubicThetaPrimeRootL2 hp where
  toFun F := F.property.toLp _
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

def cubicThetaPrimeRootFiniteWeyl {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootWeylSection hp F.val,cubicThetaPrimeRootWeylSection_memLp hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootFiniteWeyl_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootFiniteSections hp) :
    ‖cubicThetaPrimeRootFiniteValue hp (cubicThetaPrimeRootFiniteWeyl hp F)‖=
      ‖cubicThetaPrimeRootFiniteValue hp F‖ :=
  cubicThetaPrimeRootWeylSection_L2_norm hp F.val F.property

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverBorel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSectionNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm

namespace OAI

/-! Actual L2 representatives of sections on the finite prime cover.
The Atkin action preserves square integrability and the exact L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaPrimeL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp ℂ 2 (cubicThetaPrimeCoverMeasure hp)

def cubicThetaPrimeSectionRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (q : CubicThetaPrimeCover hp) : ℂ :=
  F.val (cubicThetaPrimeBorelSection hp q)

lemma cubicThetaPrimeSectionRepresentative_measurable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) : Measurable (cubicThetaPrimeSectionRepresentative hp F) :=
  F.val.continuous.measurable.comp (cubicThetaPrimeBorelSection_measurable hp)

lemma cubicThetaPrimeSectionRepresentative_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (q : CubicThetaPrimeCover hp) :
    ‖cubicThetaPrimeSectionRepresentative hp F q‖=cubicThetaPrimeSectionNorm hp F q := by
  have he := cubicThetaPrimeSectionNorm_apply hp F (cubicThetaPrimeBorelSection hp q)
  rw [cubicThetaPrimeBorelSection_rightInverse hp q] at he
  exact he.symm

lemma cubicThetaPrimeAtkinSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : MemLp (cubicThetaPrimeSectionRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)) :
    MemLp (cubicThetaPrimeSectionRepresentative hp (cubicThetaPrimeAtkinSection hp F))
      2 (cubicThetaPrimeCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeSectionRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving (cubicThetaPrimeCoverAtkin_measurePreserving hp)
  simpa only [Function.comp_def,cubicThetaPrimeSectionRepresentative_norm,
    cubicThetaPrimeAtkinSection_norm] using hc

lemma cubicThetaPrimeSectionL2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : MemLp (cubicThetaPrimeSectionRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)) :
    ‖hF.toLp (cubicThetaPrimeSectionRepresentative hp F)‖^2=
      ∫ q, (cubicThetaPrimeSectionNorm hp F q)^2 ∂cubicThetaPrimeCoverMeasure hp := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with q hq
  rw [hq,cubicThetaPrimeSectionRepresentative_norm]

lemma cubicThetaPrimeAtkinSection_L2_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : MemLp (cubicThetaPrimeSectionRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)) :
    ‖(cubicThetaPrimeAtkinSection_memLp hp F hF).toLp
      (cubicThetaPrimeSectionRepresentative hp (cubicThetaPrimeAtkinSection hp F))‖=
      ‖hF.toLp (cubicThetaPrimeSectionRepresentative hp F)‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeSectionL2_norm_sq,cubicThetaPrimeSectionL2_norm_sq]
  exact cubicThetaPrimeAtkinSection_mass hp F

def cubicThetaPrimeFiniteSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeSections hp) where
  carrier := {F | MemLp (cubicThetaPrimeSectionRepresentative hp F) 2 (cubicThetaPrimeCoverMeasure hp)}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

def cubicThetaPrimeFiniteValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteSections hp →ₗ[ℂ] CubicThetaPrimeL2 hp where
  toFun F := F.property.toLp _
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

def cubicThetaPrimeFiniteAtkin {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteSections hp →ₗ[ℂ] cubicThetaPrimeFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeAtkinSection hp F.val,cubicThetaPrimeAtkinSection_memLp hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeFiniteAtkin_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    ‖cubicThetaPrimeFiniteValue hp (cubicThetaPrimeFiniteAtkin hp F)‖=
      ‖cubicThetaPrimeFiniteValue hp F‖ :=
  cubicThetaPrimeAtkinSection_L2_norm hp F.val F.property

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootOperators

namespace OAI

/-! Actual sections and their fractional translations at the cube modulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev cubicThetaPrimeCubeRootSections (p : Eisenstein) := cubicThetaPrimeRootSections (p^3)

lemma cubicThetaPrimeCubeRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeCubeRootElement hp x • (g.val • y)=
      (cubicThetaPrimeCubeRootConjugate hp x g).val • (cubicThetaPrimeCubeRootElement hp x • y) := by
  change cubicThetaPrimeCubeRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val •
      (cubicThetaPrimeCubeRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootElement_intertwines]

lemma cubicThetaPrimeCubeRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeCubeRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeCubeRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeCubeRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeCubeRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeCubeRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeCubeRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeRootElement hp x • y)
    rw [cubicThetaPrimeCubeRootPoint_intertwines,F.property,cubicThetaPrimeCubeRootConjugate_kubota]⟩

lemma cubicThetaPrimeCubeRootSectionTranslate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootSectionTranslate hp (x+y) F=
      cubicThetaPrimeCubeRootSectionTranslate hp x (cubicThetaPrimeCubeRootSectionTranslate hp y F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp (x+y) • z)=
    F.val (cubicThetaPrimeCubeRootElement hp y • (cubicThetaPrimeCubeRootElement hp x • z))
  rw [←mul_smul,←cubicThetaPrimeCubeRootElement_add,add_comm]

@[simp] lemma cubicThetaPrimeCubeRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeCubeRootElement_zero,one_smul]

lemma cubicThetaPrimeCubeRootSectionTranslate_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootSectionTranslate hp (p^3*x) F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeCubeRootElement hp (p^3*x) • y)=F.val y
  rw [cubicThetaPrimeCubeRootElement_integral,cubicThetaPrimeRootSection_integral]

def cubicThetaPrimeCubeRootOperator {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p where
  toFun := cubicThetaPrimeCubeRootSectionTranslate hp x
  invFun := cubicThetaPrimeCubeRootSectionTranslate hp (-x)
  left_inv F := by
    rw [←cubicThetaPrimeCubeRootSectionTranslate_add,neg_add_cancel,
      cubicThetaPrimeCubeRootSectionTranslate_zero]
  right_inv F := by
    rw [←cubicThetaPrimeCubeRootSectionTranslate_add,add_neg_cancel,
      cubicThetaPrimeCubeRootSectionTranslate_zero]
  map_add' _F _G := rfl
  map_smul' _a _F := rfl

theorem cubicThetaPrimeCubeRootOperator_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p^3∣x-y) :
    cubicThetaPrimeCubeRootOperator hp x=cubicThetaPrimeCubeRootOperator hp y := by
  obtain ⟨z,hz⟩ := hxy
  have hx : x=y+p^3*z := by linear_combination hz
  apply LinearEquiv.ext
  intro F
  change cubicThetaPrimeCubeRootSectionTranslate hp x F=
    cubicThetaPrimeCubeRootSectionTranslate hp y F
  rw [hx,cubicThetaPrimeCubeRootSectionTranslate_add,cubicThetaPrimeCubeRootSectionTranslate_integral]

end CubicFirstMoment

end

end OAI

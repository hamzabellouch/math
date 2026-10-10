import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootOperators

namespace OAI

/-! Actual sections and their fractional translations at the cube modulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev cubicThetaPrimeDoubleRootSections (p : Eisenstein) := cubicThetaPrimeRootSections (p^2)

lemma cubicThetaPrimeDoubleRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeDoubleRootElement hp x • (g.val • y)=
      (cubicThetaPrimeDoubleRootConjugate hp x g).val • (cubicThetaPrimeDoubleRootElement hp x • y) := by
  change cubicThetaPrimeDoubleRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val •
      (cubicThetaPrimeDoubleRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootElement_intertwines]

lemma cubicThetaPrimeDoubleRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeDoubleRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeDoubleRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeDoubleRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeDoubleRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeDoubleRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeDoubleRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeDoubleRootElement hp x • y)
    rw [cubicThetaPrimeDoubleRootPoint_intertwines,F.property,cubicThetaPrimeDoubleRootConjugate_kubota]⟩

lemma cubicThetaPrimeDoubleRootSectionTranslate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (F : cubicThetaPrimeDoubleRootSections p) :
    cubicThetaPrimeDoubleRootSectionTranslate hp (x+y) F=
      cubicThetaPrimeDoubleRootSectionTranslate hp x (cubicThetaPrimeDoubleRootSectionTranslate hp y F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeDoubleRootElement hp (x+y) • z)=
    F.val (cubicThetaPrimeDoubleRootElement hp y • (cubicThetaPrimeDoubleRootElement hp x • z))
  rw [←mul_smul,←cubicThetaPrimeDoubleRootElement_add,add_comm]

@[simp] lemma cubicThetaPrimeDoubleRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeDoubleRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeDoubleRootElement_zero,one_smul]

lemma cubicThetaPrimeDoubleRootSectionTranslate_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeDoubleRootSections p) :
    cubicThetaPrimeDoubleRootSectionTranslate hp (p^2*x) F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeDoubleRootElement hp (p^2*x) • y)=F.val y
  rw [cubicThetaPrimeDoubleRootElement_integral,cubicThetaPrimeRootSection_integral]

def cubicThetaPrimeDoubleRootOperator {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeDoubleRootSections p ≃ₗ[ℂ] cubicThetaPrimeDoubleRootSections p where
  toFun := cubicThetaPrimeDoubleRootSectionTranslate hp x
  invFun := cubicThetaPrimeDoubleRootSectionTranslate hp (-x)
  left_inv F := by
    rw [←cubicThetaPrimeDoubleRootSectionTranslate_add,neg_add_cancel,
      cubicThetaPrimeDoubleRootSectionTranslate_zero]
  right_inv F := by
    rw [←cubicThetaPrimeDoubleRootSectionTranslate_add,add_neg_cancel,
      cubicThetaPrimeDoubleRootSectionTranslate_zero]
  map_add' _F _G := rfl
  map_smul' _a _F := rfl

theorem cubicThetaPrimeDoubleRootOperator_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p^2∣x-y) :
    cubicThetaPrimeDoubleRootOperator hp x=cubicThetaPrimeDoubleRootOperator hp y := by
  obtain ⟨z,hz⟩ := hxy
  have hx : x=y+p^2*z := by linear_combination hz
  apply LinearEquiv.ext
  intro F
  change cubicThetaPrimeDoubleRootSectionTranslate hp x F=
    cubicThetaPrimeDoubleRootSectionTranslate hp y F
  rw [hx,cubicThetaPrimeDoubleRootSectionTranslate_add,cubicThetaPrimeDoubleRootSectionTranslate_integral]

end CubicFirstMoment

end

end OAI

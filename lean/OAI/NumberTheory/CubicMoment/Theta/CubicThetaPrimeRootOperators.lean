import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootTranslation

namespace OAI

/-! Actual linear root translations on the finite-cover section space.
Integral translations act trivially, so the operators depend only on the
residue class of their parameter modulo the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootIntegralTranslation (p x : Eisenstein) :
    cubicThetaPrimeRootSubgroup p :=
  ⟨cubicThetaPrincipalTranslation x,by
    constructor <;> simp [cubicThetaPrincipalTranslation]⟩

lemma cubicThetaPrimeRootSection_integral {p : Eisenstein}
    (F : cubicThetaPrimeRootSections p) (x : Eisenstein) (y : CubicThetaPoint) :
    F.val (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) • y)=F.val y := by
  have he := F.property (cubicThetaPrimeRootIntegralTranslation p x) y
  change F.val (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) • y)=
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)*F.val y at he
  simpa only [cubicThetaPrincipalTranslation_value,one_mul] using he

lemma cubicThetaPrimeRootSectionTranslate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootSectionTranslate hp (x+y) F=
      cubicThetaPrimeRootSectionTranslate hp x (cubicThetaPrimeRootSectionTranslate hp y F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp (x+y) • z)=
    F.val (cubicThetaPrimeRootElement hp y • (cubicThetaPrimeRootElement hp x • z))
  rw [←mul_smul,←cubicThetaPrimeRootElement_add,add_comm]

@[simp] lemma cubicThetaPrimeRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeRootElement_zero,one_smul]

lemma cubicThetaPrimeRootSectionTranslate_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootSectionTranslate hp (p*x) F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeRootElement hp (p*x) • y)=F.val y
  rw [cubicThetaPrimeRootElement_integral,cubicThetaPrimeRootSection_integral]

def cubicThetaPrimeRootOperator {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeRootSections p ≃ₗ[ℂ] cubicThetaPrimeRootSections p where
  toFun := cubicThetaPrimeRootSectionTranslate hp x
  invFun := cubicThetaPrimeRootSectionTranslate hp (-x)
  left_inv F := by
    rw [←cubicThetaPrimeRootSectionTranslate_add,neg_add_cancel,
      cubicThetaPrimeRootSectionTranslate_zero]
  right_inv F := by
    rw [←cubicThetaPrimeRootSectionTranslate_add,add_neg_cancel,
      cubicThetaPrimeRootSectionTranslate_zero]
  map_add' F G := rfl
  map_smul' a F := rfl

theorem cubicThetaPrimeRootOperator_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p∣x-y) :
    cubicThetaPrimeRootOperator hp x=cubicThetaPrimeRootOperator hp y := by
  obtain ⟨z,hz⟩ := hxy
  have hx : x=y+p*z := by linear_combination hz
  apply LinearEquiv.ext
  intro F
  change cubicThetaPrimeRootSectionTranslate hp x F=
    cubicThetaPrimeRootSectionTranslate hp y F
  rw [hx,cubicThetaPrimeRootSectionTranslate_add,
    cubicThetaPrimeRootSectionTranslate_integral]

end CubicFirstMoment

end

end OAI

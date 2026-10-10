import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhat

namespace OAI

/-! The nonzero Bruhat branches act on actual global sections by the
reciprocal root parameter and its cubic symbol. The zero branch retains
the literal squared-prime dilation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicSymbol p (3*y) • cubicThetaPrimeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp y • (cubicThetaPrimeRootWeylElement hp • z))=
    cubicSymbol p (3*y)*(cubicThetaInversionSection F).val (cubicThetaPrimeRootElement hp (-x) • z)
  have he := cubicThetaPrimeRootBruhat_section hp x y hxy F (cubicThetaPrimeRootElement hp (-x) • z)
  have hx : cubicThetaPrimeRootElement hp x • (cubicThetaPrimeRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeRootElement_add,add_neg_cancel,cubicThetaPrimeRootElement_zero,one_smul]
  rw [hx] at he
  exact he

theorem cubicThetaPrimeRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrimeDilation hp.2.ne_zero • z)) := by
  change F.val (cubicThetaPrimeRootWeylElement hp • z)=_
  rw [cubicThetaPrimeRootWeylElement,cubicThetaPrimeAtkinMatrix,mul_smul,mul_smul]
  rfl

end CubicFirstMoment

end

end OAI

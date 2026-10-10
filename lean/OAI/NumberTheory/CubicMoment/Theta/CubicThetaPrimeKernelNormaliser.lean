import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinMeasure

namespace OAI

/-! Integral elements of the prime subgroup normalize its character
kernel. Their images of the constructed domain are again fundamental domains. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeKernelConj {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeCharacterKernel hp ≃ cubicThetaPrimeCharacterKernel hp where
  toFun h := ⟨g*h.val*g⁻¹,by
    change cubicThetaPrimeIwahoriCharacter p hp (g*h.val*g⁻¹)=1
    have hh : cubicThetaPrimeIwahoriCharacter p hp h.val=1 := h.property
    rw [map_mul,map_mul,hh,mul_one,map_inv,mul_inv_cancel₀]
    exact norm_ne_zero_iff.mp (by rw [cubicThetaPrimeIwahoriCharacter_norm hp g]; norm_num)⟩
  invFun h := ⟨g⁻¹*h.val*g,by
    change cubicThetaPrimeIwahoriCharacter p hp (g⁻¹*h.val*g)=1
    have hh : cubicThetaPrimeIwahoriCharacter p hp h.val=1 := h.property
    rw [map_mul,map_mul,hh,mul_one,map_inv,inv_mul_cancel₀]
    exact norm_ne_zero_iff.mp (by rw [cubicThetaPrimeIwahoriCharacter_norm hp g]; norm_num)⟩
  left_inv h := by apply Subtype.ext; change g⁻¹*(g*h.val*g⁻¹)*g=h.val; group
  right_inv h := by apply Subtype.ext; change g*(g⁻¹*h.val*g)*g⁻¹=h.val; group

def cubicThetaPrimeCoverConj {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : cubicThetaPrimeCoverGroup hp ≃ cubicThetaPrimeCoverGroup hp :=
  ((cubicThetaPrimeCoverGroupEquiv hp).symm.toEquiv.trans (cubicThetaPrimeKernelConj hp g)).trans
    (cubicThetaPrimeCoverGroupEquiv hp).toEquiv

lemma cubicThetaPrimeCoverConj_val {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) (h : cubicThetaPrimeCoverGroup hp) :
    (cubicThetaPrimeCoverConj hp g h).val=g.val*h.val*g.val⁻¹ := by
  obtain ⟨k,rfl⟩ := (cubicThetaPrimeCoverGroupEquiv hp).surjective h
  change (cubicThetaPrimeCoverGroupEquiv hp (cubicThetaPrimeKernelConj hp g
    ((cubicThetaPrimeCoverGroupEquiv hp).symm (cubicThetaPrimeCoverGroupEquiv hp k)))).val=_
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem cubicThetaPrimeIntegralImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    IsFundamentalDomain (cubicThetaPrimeCoverGroup hp)
      ((fun x : CubicThetaPoint => g.val • x) '' cubicThetaPrimeCoverDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCoverConj hp g⁻¹)
  intro h x
  change g.val • ((cubicThetaPrimeCoverConj hp g⁻¹ h).val • x)=h.val • (g.val • x)
  rw [cubicThetaPrimeCoverConj_val]
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI

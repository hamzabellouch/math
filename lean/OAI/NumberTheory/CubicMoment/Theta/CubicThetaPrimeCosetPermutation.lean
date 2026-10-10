import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDomain

namespace OAI

/-! Right translation permutes the actual finite right transversal of
the prime covering subgroup. The left factor remains in that subgroup. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCosetStep {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (t : cubicThetaPrimeTransversal hp) :
    cubicThetaPrimeTransversal hp :=
  ((cubicThetaPrimeTransversal_complement hp).equiv (t.val*g)).snd

lemma cubicThetaPrimeCosetStep_cancel {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (t : cubicThetaPrimeTransversal hp) :
    cubicThetaPrimeCosetStep hp g⁻¹ (cubicThetaPrimeCosetStep hp g t)=t := by
  let C := cubicThetaPrimeTransversal_complement hp
  let a := C.equiv (t.val*g)
  have he : a.fst.val*a.snd.val=t.val*g := C.equiv_fst_mul_equiv_snd _
  have hm : a.snd.val*g⁻¹=a.fst.val⁻¹*t.val := by
    calc
      _ = a.fst.val⁻¹*((a.fst.val*a.snd.val)*g⁻¹) := by group
      _ = _ := by rw [he]; group
  change (C.equiv (a.snd.val*g⁻¹)).snd=t
  rw [hm]
  change (C.equiv ((a.fst⁻¹).val*t.val)).snd=t
  rw [C.equiv_mul_left]
  exact C.equiv_snd_eq_self_of_mem_of_one_mem (cubicThetaPrimeCoverGroup hp).one_mem t.property

def cubicThetaPrimeCosetPermutation {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) :
    cubicThetaPrimeTransversal hp ≃ cubicThetaPrimeTransversal hp where
  toFun := cubicThetaPrimeCosetStep hp g
  invFun := cubicThetaPrimeCosetStep hp g⁻¹
  left_inv := cubicThetaPrimeCosetStep_cancel hp g
  right_inv t := by simpa only [inv_inv] using cubicThetaPrimeCosetStep_cancel hp g⁻¹ t

lemma cubicThetaPrimeCosetPermutation_factor {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (t : cubicThetaPrimeTransversal hp) :
    (((cubicThetaPrimeTransversal_complement hp).equiv (t.val*g)).fst.val)*
      (cubicThetaPrimeCosetPermutation hp g t).val=t.val*g :=
  (cubicThetaPrimeTransversal_complement hp).equiv_fst_mul_equiv_snd _

end CubicFirstMoment

end

end OAI

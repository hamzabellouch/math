import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSections
import Mathlib.GroupTheory.Complement

namespace OAI

/-! The finite right cosets used by the cubed-prime Hecke trace. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeIwahori_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeIwahori (p^3)).FiniteIndex :=
  cubicThetaPrimeIwahori_finiteIndex (pow_ne_zero 3 hp.2.ne_zero)

def cubicThetaPrimeCubeTransversal (p : Eisenstein) : Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeIwahori (p^3)).exists_isComplement_right 1)

lemma cubicThetaPrimeCubeTransversal_complement (p : Eisenstein) :
    Subgroup.IsComplement (cubicThetaPrimeIwahori (p^3)) (cubicThetaPrimeCubeTransversal p) :=
  (Classical.choose_spec ((cubicThetaPrimeIwahori (p^3)).exists_isComplement_right 1)).1

lemma cubicThetaPrimeCubeTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeTransversal p) := by
  let := cubicThetaPrimeCubeIwahori_finiteIndex hp
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeTransversal_complement p).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCubeCosetStep (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) : cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv (t.val*g)).snd

lemma cubicThetaPrimeCubeCosetStep_cancel (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeCosetStep p g⁻¹ (cubicThetaPrimeCubeCosetStep p g t)=t := by
  let C := cubicThetaPrimeCubeTransversal_complement p
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
  exact C.equiv_snd_eq_self_of_mem_of_one_mem (cubicThetaPrimeIwahori (p^3)).one_mem t.property

def cubicThetaPrimeCubeCosetPermutation (p : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeTransversal p ≃ cubicThetaPrimeCubeTransversal p where
  toFun := cubicThetaPrimeCubeCosetStep p g
  invFun := cubicThetaPrimeCubeCosetStep p g⁻¹
  left_inv := cubicThetaPrimeCubeCosetStep_cancel p g
  right_inv t := by simpa only [inv_inv] using cubicThetaPrimeCubeCosetStep_cancel p g⁻¹ t

lemma cubicThetaPrimeCubeCosetPermutation_factor (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) :
    (((cubicThetaPrimeCubeTransversal_complement p).equiv (t.val*g)).fst.val)*
      (cubicThetaPrimeCubeCosetPermutation p g t).val=t.val*g :=
  (cubicThetaPrimeCubeTransversal_complement p).equiv_fst_mul_equiv_snd _

end CubicFirstMoment

end

end OAI

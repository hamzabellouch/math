import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReciprocalNormalizer
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTrace

namespace OAI

/-! Integral normalizers permute the actual finite cosets of the
cubed-prime trace. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeNormalizerStep (p : Eisenstein) (δ : SL(2,Eisenstein))
    (t : cubicThetaPrimeCubeTransversal p) : cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv (cubicThetaPrincipalConjugate δ t.val)).snd

lemma cubicThetaPrimeCubeNormalizerStep_cancel (p : Eisenstein) (δ : SL(2,Eisenstein))
    (hδ : p^3∣δ.val 1 0) (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeNormalizerStep p δ⁻¹ (cubicThetaPrimeCubeNormalizerStep p δ t)=t := by
  let C := cubicThetaPrimeCubeTransversal_complement p
  let a := C.equiv (cubicThetaPrincipalConjugate δ t.val)
  have he : a.fst.val*a.snd.val=cubicThetaPrincipalConjugate δ t.val := C.equiv_fst_mul_equiv_snd _
  have hi : p^3∣(δ⁻¹).val 1 0 := by
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hδ
  let h : cubicThetaPrimeIwahori (p^3) :=
    ⟨cubicThetaPrincipalConjugate δ⁻¹ a.fst.val,
      cubicThetaPrimeIwahori_integral_conjugate (p^3) δ⁻¹ hi a.fst⟩
  have hm : h.val*cubicThetaPrincipalConjugate δ⁻¹ a.snd.val=t.val := by
    apply Subtype.ext
    have he' := congrArg (fun g : cubicThetaPrincipalGroup => g.val) he
    change ((δ⁻¹)⁻¹*a.fst.val.val*δ⁻¹)*((δ⁻¹)⁻¹*a.snd.val.val*δ⁻¹)=t.val.val
    rw [inv_inv]
    change a.fst.val.val*a.snd.val.val=δ⁻¹*t.val.val*δ at he'
    calc
      _ = δ*(a.fst.val.val*a.snd.val.val)*δ⁻¹ := by group
      _ = _ := by rw [he']; group
  have hx : cubicThetaPrincipalConjugate δ⁻¹ a.snd.val=h.val⁻¹*t.val :=
    (eq_inv_mul_iff_mul_eq).mpr hm
  change (C.equiv (cubicThetaPrincipalConjugate δ⁻¹ a.snd.val)).snd=t
  rw [hx]
  change (C.equiv ((h⁻¹).val*t.val)).snd=t
  rw [C.equiv_mul_left]
  exact C.equiv_snd_eq_self_of_mem_of_one_mem (cubicThetaPrimeIwahori (p^3)).one_mem t.property

def cubicThetaPrimeCubeNormalizerPermutation (p : Eisenstein) (δ : SL(2,Eisenstein))
    (hδ : p^3∣δ.val 1 0) : cubicThetaPrimeCubeTransversal p ≃ cubicThetaPrimeCubeTransversal p where
  toFun := cubicThetaPrimeCubeNormalizerStep p δ
  invFun := cubicThetaPrimeCubeNormalizerStep p δ⁻¹
  left_inv := cubicThetaPrimeCubeNormalizerStep_cancel p δ hδ
  right_inv t := by
    have hi : p^3∣(δ⁻¹).val 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hδ
    simpa only [inv_inv] using cubicThetaPrimeCubeNormalizerStep_cancel p δ⁻¹ hi t

lemma cubicThetaPrimeCubeTrace_normalizer {p : Eisenstein} (hp : primaryPrime p)
    (δ : SL(2,Eisenstein)) (hδ : p^3∣δ.val 1 0)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    (∑' t : cubicThetaPrimeCubeTransversal p,
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrincipalConjugate δ t.val) x)=
      (cubicThetaPrimeCubeTraceSection hp F).val x := by
  have ht (t : cubicThetaPrimeCubeTransversal p) :
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrincipalConjugate δ t.val) x=
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeNormalizerPermutation p δ hδ t).val x := by
    rw [←(cubicThetaPrimeCubeTransversal_complement p).equiv_fst_mul_equiv_snd
      (cubicThetaPrincipalConjugate δ t.val),cubicThetaPrimeCubeTraceTerm_left]
    rfl
  simp_rw [ht]
  exact (cubicThetaPrimeCubeNormalizerPermutation p δ hδ).tsum_eq
    (fun t => cubicThetaPrimeCubeTraceTerm p F t.val x)

end CubicFirstMoment

end

end OAI

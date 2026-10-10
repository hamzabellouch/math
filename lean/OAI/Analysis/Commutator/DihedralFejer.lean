import Mathlib
import OAI.Analysis.Commutator.DihedralHaar
import OAI.Analysis.Commutator.FejerTest
import OAI.Analysis.Commutator.TracialDevelopment

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.DihedralCorner

open FreeMoments FejerTest

variable {A : Type*} [CStarAlgebra A]

lemma star_pow_mul_pow (u : unitary A) (i j : ℕ) :
    star ((u:A)^i)*(u:A)^j=wave u (-(i:ℤ)+(j:ℤ)) := by
  rw [←wave_nat,←wave_nat,wave_star,←wave_add]

lemma testPolynomial_expansion (u : unitary A) (m : ℕ) :
    testPolynomial (u:A) m=
      ((m:ℂ)⁻¹*(m:ℂ)⁻¹) •
        (∑ i∈Finset.range m,∑ j∈Finset.range m,wave u (-(i:ℤ)+(j:ℤ))) -
      (m:ℂ)⁻¹ • (1:A) := by
  have hs : star ((m:ℂ)⁻¹)=(m:ℂ)⁻¹ := by simp
  simp only [testPolynomial,powerAverage,star_smul,
    star_sum,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    star_pow_mul_pow,hs,←Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

lemma testPolynomial_reflection_commute (u d : unitary A)
    (hr : MulAut.conj d u=u⁻¹) (m : ℕ) :
    (d:A)*testPolynomial (u:A) m=testPolynomial (u:A) m*(d:A) := by
  rw [testPolynomial_expansion]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  congr 1
  congr 1
  simp only [Finset.mul_sum,Finset.sum_mul,reflection_wave u d hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

variable {p : A} (hp : IsStarProjection p)

def compressCorner : A →ₗ[ℂ] Corner hp where
  toFun a := ⟨p*a*p,by constructor <;> simp only [mul_assoc,←mul_assoc p p,hp.isIdempotentElem.eq]⟩
  map_add' a b := by
    apply Subtype.ext
    change p*(a+b)*p=p*a*p+p*b*p
    rw [mul_add,add_mul]
  map_smul' z a := by
    apply Subtype.ext
    change p*(z • a)*p=z • (p*a*p)
    simp only [mul_smul_comm,smul_mul_assoc]

@[simp] lemma compressCorner_coe (a : A) : ((compressCorner hp a:Corner hp):A)=p*a*p := rfl

@[simp] lemma compressCorner_one : compressCorner hp 1=1 := by
  apply Subtype.ext
  change p*1*p=p
  rw [mul_one,hp.isIdempotentElem.eq]

@[simp] lemma compressCorner_wave (u : unitary A) (n : ℤ) :
    compressCorner hp (wave u n)=cosine u hp n := rfl

def fejerCorner (u : unitary A) (m : ℕ) : Corner hp :=
  compressCorner hp (testPolynomial (u:A) m)

lemma fejerCorner_mem (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (hdp : (d:A)*p=p) (m : ℕ) :
    fejerCorner hp u m∈cosineAlgebra u d hr hp hpform hdp := by
  let R := cosineAlgebra u d hr hp hpform hdp
  unfold fejerCorner
  rw [testPolynomial_expansion]
  simp only [map_sub,map_smul,map_sum,compressCorner_wave,compressCorner_one]
  exact R.sub_mem (R.smul_mem (R.sum_mem (fun i _ =>
    R.sum_mem (fun j _ => cosine_mem u hp _))) _) (R.smul_mem R.one_mem _)

lemma fejerCorner_selfAdjoint (u : unitary A) (m : ℕ) :
    IsSelfAdjoint (fejerCorner hp u m) := by
  change star (fejerCorner hp u m)=fejerCorner hp u m
  apply Subtype.ext
  change star (p*testPolynomial (u:A) m*p)=p*testPolynomial (u:A) m*p
  simp only [star_mul,hp.isSelfAdjoint.star_eq,(testPolynomial_selfAdjoint (u:A) m).star_eq]
  exact (mul_assoc _ _ _).symm

lemma fejerCorner_coe_right (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (m : ℕ) :
    ((fejerCorner hp u m:Corner hp):A)=testPolynomial (u:A) m*p := by
  change p*testPolynomial (u:A) m*p=_
  have comm : p*testPolynomial (u:A) m=testPolynomial (u:A) m*p := by
    rw [hpform]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,one_mul,mul_one,
      testPolynomial_reflection_commute u d hr]
  rw [comm,mul_assoc,hp.isIdempotentElem.eq]

lemma fejerCorner_norm_le (u : unitary A) (m : ℕ) (hm : 0 < m) :
    ‖fejerCorner hp u m‖≤2 := by
  nontriviality A
  change ‖p*testPolynomial (u:A) m*p‖≤2
  have hp1 : ‖p‖≤1 := hp.norm_le
  have hq := norm_testPolynomial_le (u:A) m hm (le_of_eq (CStarRing.norm_coe_unitary u))
  calc
    _ ≤ ‖p‖*‖testPolynomial (u:A) m‖*‖p‖ := norm_mul₃_le
    _ ≤ 1*2*1 := mul_le_mul
      (mul_le_mul hp1 hq (norm_nonneg _) zero_le_one) hp1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (h1 : φ 1=1) (htr : ∀ a b : A, φ (a*b)=φ (b*a))
  (hstar : ∀ a : A, φ (star a)=star (φ a)) (hfree : Free S φ.toLinearMap)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d:A)∈S i) (hs : (s:A)∈S j)
  (hd0 : φ (d:A)=0) (hs0 : φ (s:A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d:A)*(d:A)=1)

variable (hpform : p=(1/2:ℂ) • (1+(d:A)))

include htr hstar hfree hij hd hs hd0 hs0 hd2 in
omit [StarOrderedRing A] in
lemma testPolynomial_reflection_trace (m : ℕ) (l : ℤ) :
    φ (wave (d*s) l*testPolynomial ((d*s:unitary A):A) m*(d:A))=0 := by
  have ht (n : ℤ) : φ (wave (d*s) n*(d:A))=0 :=
    reflection_trace φ.toLinearMap htr hstar hfree d s i j hij hd hs hd0 hs0 hd2 n
  rw [testPolynomial_expansion]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,
    Finset.mul_sum,Finset.sum_mul,←wave_add,map_sub,map_smul,map_sum,
    ht,
    smul_zero,Finset.sum_const_zero,sub_zero]

include htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_wave_trace (m : ℕ) (l : ℤ) :
    φ (wave (d*s) l*((fejerCorner hp (d*s) m:Corner hp):A))=
      (1/2:ℂ)*φ (testPolynomial ((d*s:unitary A):A) m*wave (d*s) l) := by
  rw [fejerCorner_coe_right hp (d*s) d hr hpform]
  let q := testPolynomial ((d*s:unitary A):A) m
  have he : wave (d*s) l*(q*p)=(1/2:ℂ) •
      (wave (d*s) l*q + wave (d*s) l*q*(d:A)) := by
    rw [hpform]
    simp only [mul_smul_comm,mul_add,mul_one,mul_assoc]
  rw [he]
  simp only [map_smul,map_add,smul_eq_mul]
  rw [testPolynomial_reflection_trace φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hd2,add_zero,htr]

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_centered (m : ℕ) (hm : 0 < m) :
    halfCornerTrace hp φ.toLinearMap (fejerCorner hp (d*s) m)=0 := by
  have hhaar : HaarMoments φ ((d*s:unitary A):A) :=
    dihedral_haar φ.toLinearMap h1 hstar hfree d s i j hij hd hs hd0 hs0
  have h := fejerCorner_wave_trace hp φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hr hd2 hpform m 0
  simp only [wave_zero,one_mul,mul_one,moment_testPolynomial φ _ hhaar h1 m hm,
    mul_zero] at h
  simp only [halfCornerTrace_apply,PositiveLinearMap.coe_toLinearMap,h,mul_zero]

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_positive_coefficient (m l : ℕ) (hm : 0 < m)
    (hl : 0 < l) (hlm : l < m) :
    2*φ (wave (d*s) (l:ℤ)*((fejerCorner hp (d*s) m:Corner hp):A))=
      ((m:ℂ)-(l:ℂ))/(m:ℂ)^2 := by
  rw [fejerCorner_wave_trace hp φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hr hd2 hpform, wave_nat]
  have hhaar : HaarMoments φ ((d*s:unitary A):A) :=
    dihedral_haar φ.toLinearMap h1 hstar hfree d s i j hij hd hs hd0 hs0
  rw [positive_coefficient φ _ hhaar m l hm hl hlm]
  ring

lemma corner_preGNS_norm (a : Corner hp) :
    ‖(cornerFunctional hp φ (1/2) (by norm_num)).toPreGNS a‖=
      Real.sqrt 2*‖φ.toPreGNS (a:A)‖ := by
  rw [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,cornerFunctional_apply,
    corner_mul,corner_star]
  norm_num only [one_div,inv_inv]
  rw [Complex.smul_re,smul_eq_mul,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]

include h1 htr hstar hfree hij hd hs hd0 hs0 hr hpform in
lemma fejerCorner_preGNS_norm (m : ℕ) (hm : 0 < m) :
    ‖(cornerFunctional hp φ (1/2) (by norm_num)).toPreGNS (fejerCorner hp (d*s) m)‖≤
      2*Real.sqrt 2*Real.sqrt ((m:ℝ)⁻¹) := by
  have hhaar : HaarMoments φ ((d*s:unitary A):A) :=
    dihedral_haar φ.toLinearMap h1 hstar hfree d s i j hij hd hs hd0 hs0
  have hu : ‖((d*s:unitary A):A)‖≤1 := by
    nontriviality A
    exact le_of_eq (CStarRing.norm_coe_unitary _)
  have hq := norm_preGNS_testPolynomial φ _ hhaar h1 m hm hu
  rw [corner_preGNS_norm,fejerCorner_coe_right hp (d*s) d hr hpform]
  have hmul : ‖φ.toPreGNS (testPolynomial ((d*s:unitary A):A) m*p)‖≤
      ‖φ.toPreGNS (testPolynomial ((d*s:unitary A):A) m)‖ := by
    exact ((TracialGNS.rightMulPre φ htr p).le_opNorm
      (φ.toPreGNS (testPolynomial ((d*s:unitary A):A) m))).trans
      ((mul_le_mul_of_nonneg_right
        ((TracialGNS.norm_rightMulPre_le φ htr p).trans hp.norm_le) (norm_nonneg _)).trans_eq
        (one_mul _))
  calc
    _ ≤ Real.sqrt 2*(2*Real.sqrt ((m:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (hmul.trans hq) (Real.sqrt_nonneg _)
    _ = _ := by ring

end Kadison.DihedralCorner

end

end
end

end OAI

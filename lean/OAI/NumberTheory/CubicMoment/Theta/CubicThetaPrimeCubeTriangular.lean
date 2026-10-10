import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReductionRow

namespace OAI

/-! Exact triangularization of the nonzero valuation branches in the
cubed-prime trace. The matrices are the actual integral row completions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeReducedScale {p : Eisenstein} (_hp : primaryPrime p) (k : Fin 3) : ℂ :=
  (p:ℂ)^(3-k.val)/cubicThetaPrimeSquareRoot (p^3)

lemma cubicThetaPrimeCubeReducedScale_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : cubicThetaPrimeCubeReducedScale hp k≠0 :=
  div_ne_zero (pow_ne_zero _ (fun hz => hp.2.ne_zero (Subtype.ext hz)))
    (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero))

def cubicThetaPrimeCubeReducedMatrix {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : SL(2,ℂ) :=
  cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn)*
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*
    cubicThetaPrincipalComplex (cubicThetaPrincipalLower (p^k.val*n))

lemma cubicThetaPrimeCubeReducedMatrix_c {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 1 0=0 := by
  let q := cubicThetaPrimeSquareRoot (p^3)
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hs : q^2=(p:ℂ)^3 := by
    exact (cubicThetaPrimeSquareRoot_sq (p^3)).trans
      (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have he : (p:ℂ)^(3-k.val)*(p:ℂ)^k.val=(p:ℂ)^3 := by
    rw [←pow_add]
    congr 1
    omega
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0)=0
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*q+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*0)*1+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*q⁻¹)*
        ((3*(p^k.val*n):Eisenstein):ℂ)=0
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d]
  push_cast
  rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from
    map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
  simp only [mul_zero,zero_add,add_zero,mul_one]
  calc
    _ = (3*(n:ℂ)/q)*((p:ℂ)^(3-k.val)*(p:ℂ)^k.val-q^2) := by
      field_simp
      ring
    _ = 0 := by rw [he,hs,sub_self,mul_zero]

lemma cubicThetaPrimeCubeReducedMatrix_d {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 1 1=cubicThetaPrimeCubeReducedScale hp k := by
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1)=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*
      cubicThetaPrimeSquareRoot (p^3)+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*0)*0+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*
        (cubicThetaPrimeSquareRoot (p^3))⁻¹)*1=_
  rw [cubicThetaPrimeCubeReduction_d]
  push_cast
  simp [cubicThetaPrimeCubeReducedScale,div_eq_mul_inv]

lemma cubicThetaPrimeCubeReducedMatrix_b {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 0 1=
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
        cubicThetaPrimeSquareRoot (p^3) := by
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1)=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 0:Eisenstein):ℂ)*
      cubicThetaPrimeSquareRoot (p^3)+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)*0)*0+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)*
        (cubicThetaPrimeSquareRoot (p^3))⁻¹)*1=_
  simp [div_eq_mul_inv]

lemma cubicThetaPrimeCubeReducedMatrix_a {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 0 0=(cubicThetaPrimeCubeReducedScale hp k)⁻¹ := by
  have he := (cubicThetaPrimeCubeReducedMatrix hp k n hn).property
  rw [Matrix.det_fin_two,cubicThetaPrimeCubeReducedMatrix_c,cubicThetaPrimeCubeReducedMatrix_d,
    mul_zero,sub_zero] at he
  exact eq_inv_of_mul_eq_one_left he

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueStep

namespace OAI

/-! The lower-chart value is a genuine function modulo p^3. Its scaled
versions descend to the smaller residue rings used in the valuation split. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipalLower_add (m n : Eisenstein) :
    cubicThetaPrincipalLower (m+n)=cubicThetaPrincipalLower m*cubicThetaPrincipalLower n := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1,0;3*(m+n),1] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,0;3*m,1]*!![1,0;3*n,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  ring

lemma cubicThetaPrincipalLower_zero : cubicThetaPrincipalLower 0=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1,0;3*0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

def cubicThetaPrimeCubeLowerValue {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (m : Eisenstein) : ℂ :=
  F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (cubicThetaPrincipalLower m • x))

lemma cubicThetaPrimeCubeLowerValue_congr {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (m n : Eisenstein) (h : p^3∣m-n) :
    cubicThetaPrimeCubeLowerValue hp F x m=cubicThetaPrimeCubeLowerValue hp F x n := by
  let g : cubicThetaPrimeIwahori (p^3) :=
    ⟨cubicThetaPrincipalLower (m-n),dvd_mul_of_dvd_right h 3⟩
  have he := (cubicThetaPrimeCubeDilationSection hp F).property g (cubicThetaPrincipalLower n • x)
  change (cubicThetaPrimeCubeDilationSection hp F).val
    (cubicThetaPrincipalLower (m-n) • (cubicThetaPrincipalLower n • x))=
      cubicThetaKubotaValue (cubicThetaPrincipalLower (m-n))*
        (cubicThetaPrimeCubeDilationSection hp F).val (cubicThetaPrincipalLower n • x) at he
  rw [←mul_smul,←cubicThetaPrincipalLower_add,sub_add_cancel,cubicThetaPrincipalLower_value,one_mul] at he
  exact he

lemma cubicThetaPrimeCubeLowerValue_scaled_congr {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (k : Fin 3) (m n : Eisenstein)
    (h : p^(3-k.val)∣m-n) :
    cubicThetaPrimeCubeLowerValue hp F x (p^k.val*m)=
      cubicThetaPrimeCubeLowerValue hp F x (p^k.val*n) := by
  apply cubicThetaPrimeCubeLowerValue_congr hp F x
  rw [show p^3=p^k.val*p^(3-k.val) by rw [←pow_add]; congr 1; omega]
  simpa only [mul_sub] using mul_dvd_mul_left (p^k.val) h

lemma cubicThetaPrimeCubeLowerValue_canonical {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (k : Fin 3) (m : Eisenstein) :
    cubicThetaPrimeCubeLowerValue hp F x (p^k.val*
      residueRepresentative (p^(3-k.val)) (Ideal.Quotient.mk (modulus (p^(3-k.val))) m))=
      cubicThetaPrimeCubeLowerValue hp F x (p^k.val*m) := by
  apply cubicThetaPrimeCubeLowerValue_scaled_congr hp F x
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))

lemma cubicThetaPrimeCubeLowerValue_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeLowerValue hp F x 0=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x) := by
  simp [cubicThetaPrimeCubeLowerValue,cubicThetaPrincipalLower_zero]

end CubicFirstMoment

end

end OAI

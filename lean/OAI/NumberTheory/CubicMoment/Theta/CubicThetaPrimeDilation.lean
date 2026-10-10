import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeConjugationHom
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisenstein

namespace OAI

/-! The unramified arithmetic correspondence acts on the actual
hyperbolic Eisenstein family, with its cubic diagonal twist retained. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeSquareRoot (p : Eisenstein) : ℂ := (p:ℂ)^(1/2:ℂ)

lemma cubicThetaPrimeSquareRoot_ne_zero {p : Eisenstein} (hp : p≠0) :
    cubicThetaPrimeSquareRoot p≠0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (fun hz => hp (Subtype.ext hz))

lemma cubicThetaPrimeSquareRoot_sq (p : Eisenstein) :
    (cubicThetaPrimeSquareRoot p)^2=(p:ℂ) := by
  unfold cubicThetaPrimeSquareRoot
  rw [←Complex.cpow_mul_nat]
  norm_num

def cubicThetaPrimeDilation {p : Eisenstein} (hp : p≠0) : SL(2,ℂ) :=
  ⟨!![cubicThetaPrimeSquareRoot p,0;0,(cubicThetaPrimeSquareRoot p)⁻¹],by
    simp [Matrix.det_fin_two,cubicThetaPrimeSquareRoot_ne_zero hp]⟩

theorem cubicThetaPrimeDilation_intertwines {p : Eisenstein} (hp : primary p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeDilation (primary_ne_zero hp)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp g)*
        cubicThetaPrimeDilation (primary_ne_zero hp) := by
  have hq := cubicThetaPrimeSquareRoot_ne_zero (primary_ne_zero hp)
  have hs := cubicThetaPrimeSquareRoot_sq p
  have hc : (p:ℂ)*(g.val.val 1 0/p:Eisenstein)=g.val.val 1 0 := by
    exact_mod_cast cubicThetaPrimeIwahori_division (primary_ne_zero hp) g
  apply Subtype.ext
  change ((cubicThetaPrimeDilation (primary_ne_zero hp):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrincipalComplex g.val:Matrix (Fin 2) (Fin 2) ℂ))=
    ((cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp g):Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (primary_ne_zero hp):Matrix (Fin 2) (Fin 2) ℂ))
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,mul_comm]
  · simp only [Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeDilation,cubicThetaPrincipalComplex_apply,cubicThetaPrimeConjugate,
      cubicThetaPrimeConjugatedMatrix]
    simp
    field_simp
    linear_combination (g.val.val 0 1:ℂ)*hs
  · simp only [Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeDilation,cubicThetaPrincipalComplex_apply,cubicThetaPrimeConjugate,
      cubicThetaPrimeConjugatedMatrix]
    simp
    field_simp
    linear_combination -(g.val.val 1 0/p:Eisenstein)*hs-hc
  · simp [cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,mul_comm]

theorem cubicThetaEisenstein_prime_dilation_twist {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero)
        (cubicThetaMobius (cubicThetaPrincipalComplex g.val) z)) s=
      star (cubicThetaPrimeIwahoriCharacter p hp g)*cubicThetaKubotaValue g.val*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp.2.ne_zero) z) s := by
  have hunit : star (cubicThetaPrimeIwahoriCharacter p hp g)*
      cubicThetaPrimeIwahoriCharacter p hp g=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaPrimeIwahoriCharacter_norm hp g]
    norm_num
  rw [cubicThetaMobius_comp,cubicThetaPrimeDilation_intertwines hp.1,
    ←cubicThetaMobius_comp,cubicThetaEisenstein_automorphy
      (cubicThetaPrimeConjugate hp.1 g)
      (cubicThetaMobius_height_pos _ hz),cubicThetaPrimeConjugate_kubota hp g]
  · rw [←mul_assoc,hunit,one_mul]
  · exact hz
  · exact hz

end CubicFirstMoment

end

end OAI

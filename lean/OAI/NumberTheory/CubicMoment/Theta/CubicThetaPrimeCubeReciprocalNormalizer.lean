import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeOppositeConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegralQuotient

namespace OAI

/-! The integral normalizer used to compare the cubed-prime correspondence
with its reciprocal. Its lower-left entry vanishes modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeIwahori_integral_conjugate (q : Eisenstein)
    (δ : SL(2,Eisenstein)) (hδ : q∣δ.val 1 0)
    (g : cubicThetaPrimeIwahori q) :
    cubicThetaPrincipalConjugate δ g.val∈cubicThetaPrimeIwahori q := by
  change q∣(δ⁻¹*g.val.val*δ) 1 0
  have he : (δ⁻¹*g.val.val*δ) 1 0=
      (δ.val 0 0)^2*g.val.val 1 0-(δ.val 1 0)^2*g.val.val 0 1+
        δ.val 0 0*δ.val 1 0*(g.val.val 1 1-g.val.val 0 0) := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    ring
  rw [he]
  have hc : q∣(δ.val 1 0)^2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hδ (δ.val 1 0)
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right g.property _) (dvd_mul_of_dvd_left hc _))
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _)

lemma cubicThetaPrimeIwahori_integral_conjugate_iff (q : Eisenstein)
    (δ : SL(2,Eisenstein)) (hδ : q∣δ.val 1 0) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalConjugate δ g∈cubicThetaPrimeIwahori q ↔ g∈cubicThetaPrimeIwahori q := by
  constructor
  · intro hg
    have hi : q∣(δ⁻¹).val 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hδ
    have hh := cubicThetaPrimeIwahori_integral_conjugate q δ⁻¹ hi ⟨_,hg⟩
    have he : cubicThetaPrincipalConjugate δ⁻¹ (cubicThetaPrincipalConjugate δ g)=g := by
      apply Subtype.ext
      simp [cubicThetaPrincipalConjugate,mul_assoc]
    rwa [he] at hh
  · intro hg
    exact cubicThetaPrimeIwahori_integral_conjugate q δ hδ ⟨g,hg⟩

def cubicThetaPrimeCubeReciprocalNormalizer {p : Eisenstein} (hp : primaryPrime p) : SL(2,Eisenstein) :=
  ((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹

lemma cubicThetaPrimeCubeReciprocalNormalizer_lower {p : Eisenstein} (hp : primaryPrime p) :
    p^3∣(cubicThetaPrimeCubeReciprocalNormalizer hp).val 1 0 := by
  have he : (cubicThetaPrimeCubeReciprocalNormalizer hp).val 1 0=
      -(cubicThetaPrimeCubeWeyl hp).val 1 1 := by
    change (Matrix.adjugate (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
      !![0,-1;1,0])) 1 0= -((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein) 1 1
    simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [he,cubicThetaPrimeCubeWeyl_d]
  exact dvd_neg.mpr (cubicThetaPrimeCubeWeylDenominator_dvd hp)

end CubicFirstMoment

end

end OAI

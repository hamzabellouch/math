import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDeepCharacter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePowerFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilation

namespace OAI

/-! Exact diagonal characters of the prime-power dilations. The second
and fourth powers below are the intermediate cubic-root branches. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimePower_primary {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    primary (p^n) := by
  induction n with
  | zero => simpa only [pow_zero] using primary_one
  | succ n ih => simpa only [pow_succ] using primary_mul ih hp.1

lemma cubicThetaPrimePowerConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (g : cubicThetaPrimeIwahori (p^n)) :
    cubicThetaKubotaValue g.val=(cubicSymbol p (g.val.val 0 0))^n*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimePower_primary hp n) g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    (cubicSymbol p (g.val.val 0 0))^n*
      cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p^n)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division (pow_ne_zero n hp.2.ne_zero) g]
  rw [cubicSymbol_mul_upper ha,cubic_reciprocity ha (cubicThetaPrimePower_primary hp n),
    cubicThetaSymbol_prime_pow hp]

lemma cubicThetaPrimePowerConjugate_kubota_star {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (g : cubicThetaPrimeIwahori (p^n)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimePower_primary hp n) g)=
      star ((cubicSymbol p (g.val.val 0 0))^n)*cubicThetaKubotaValue g.val := by
  have hc : IsCoprime (p^n) (g.val.val 0 0) :=
    ((cubicThetaPrincipalGroup_column_coprime g.val).of_isCoprime_of_dvd_right g.property).symm
  have hnorm : ‖(cubicSymbol p (g.val.val 0 0))^n‖=1 := by
    rw [←cubicThetaSymbol_prime_pow hp]
    exact norm_cubicSymbol_of_isCoprime (cubicThetaPrimePower_primary hp n) hc
  have hunit : star ((cubicSymbol p (g.val.val 0 0))^n)*(cubicSymbol p (g.val.val 0 0))^n=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',hnorm]
    norm_num
  rw [cubicThetaPrimePowerConjugate_kubota hp n g,←mul_assoc,hunit,one_mul]

theorem cubicThetaPrimePowerDilation_transform {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (g : cubicThetaPrimeIwahori (p^n)) (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • (g.val • x))=
      star ((cubicSymbol p (g.val.val 0 0))^n)*cubicThetaKubotaValue g.val*
        F.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x) := by
  change F.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) •
    (cubicThetaPrincipalComplex g.val • x))=_
  rw [←mul_smul,cubicThetaPrimeDilation_intertwines (cubicThetaPrimePower_primary hp n) g,mul_smul]
  change F.val (cubicThetaPrimeConjugate (cubicThetaPrimePower_primary hp n) g •
    (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x))=_
  rw [F.property,cubicThetaPrimePowerConjugate_kubota_star hp n g]

end CubicFirstMoment

end

end OAI

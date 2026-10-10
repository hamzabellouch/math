import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTriangular

namespace OAI

/-! The cubic phase of each triangularized branch is the corresponding
power of the numerator character of its upper-right entry. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReduction_top_congruence {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    p∣3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1-1 := by
  have he := cubicThetaPrimeCubeReduction_determinant hp k n hn
  have hpw : p∣p^(3-k.val) := dvd_pow_self p (by have := k.isLt; omega)
  rw [show 3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1-1=
    -((cubicThetaPrimeCubeReduction hp k n hn).val 0 0*p^(3-k.val)) by
      linear_combination he]
  exact dvd_neg.mpr (dvd_mul_of_dvd_right hpw _)

theorem cubicThetaPrimeCubeReduction_phase_top {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))=
      (cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1))^k.val := by
  let c := cubicSymbol p (3*n)
  let d := cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1)
  have hcd : c*d=1 := by
    dsimp only [c,d]
    rw [←cubicSymbol_mul_upper hp.1,cubicSymbol_congr
      (residue_eq_of_dvd_sub (cubicThetaPrimeCubeReduction_top_congruence hp k n hn))]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  have hc3 : c^3=1 := cubicSymbol_cube_of_isCoprime hp.1 _
    ((primary_coprime_three hp.1).mul_right (hp.2.coprime_iff_not_dvd.mpr hn))
  have hd : d=c^2 := by linear_combination c^2*hcd-d*hc3
  have hc : c=d^2 := by
    rw [hd]
    calc
      c = c*c^3 := by rw [hc3,mul_one]
      _ = (c^2)^2 := by ring
  rw [cubicThetaPrimeCubeReduction_phase hp]
  change c^(3-k.val)=d^k.val
  fin_cases k
  · simpa only [pow_zero] using hc3
  · simpa only [pow_one] using hd.symm
  · simpa only [Nat.reduceSub,pow_one] using hc

theorem cubicThetaPrimeCubeReduction_section {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalLower (p^k.val*n) • x))=
      (cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1))^k.val*
        F.val (cubicThetaPrimeCubeReducedMatrix hp k n hn • x) := by
  rw [←cubicThetaPrimeCubeReduction_phase_top hp]
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [cubicThetaPrimeCubeReducedMatrix,mul_smul,mul_smul]
  change _=star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))*
    F.val (cubicThetaPrimeCubeReduction hp k n hn •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (p^k.val*n) • x)))
  rw [F.property,←mul_assoc,hu,one_mul]

end CubicFirstMoment

end

end OAI

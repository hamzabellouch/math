import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedTopPhase

namespace OAI

/-! The forcing in the actual ramified unit system is the same explicit
modulus-nine phase, multiplied by the primary base residue. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaRamifiedForcing_phase {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    (∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
        cubicThetaArithmeticFourierResidue (h*omegaE^(j:ℕ)*(e:Eisenstein)) (4/3))=
      ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3) := by
  let d : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
  have hd : (d:Eisenstein)=omegaE^(j:ℕ) := by
    simp only [d,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
  let F (e : Eisensteinˣ) :=
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
      cubicThetaArithmeticFourierResidue (h*omegaE^(j:ℕ)*(e:Eisenstein)) (4/3)
  have hpos : F (d⁻¹)=0 := by
    have hi : ((d⁻¹:Eisensteinˣ):Eisenstein)=omegaE^(cubicThetaInverseUnitIndex j:ℕ) := by
      have he := cubicThetaNegativeInverseUnit_power j
      change -((d⁻¹:Eisensteinˣ):Eisenstein)=_ at he
      exact neg_inj.mp he
    have hz := cubicThetaRamifiedTopFactor_positive_zero (d⁻¹)
      (cubicThetaLambda_dvd_primary_omega_sub_one hh j)
      (hi ▸ cubicThetaLambda_dvd_omega_pow_sub_one (cubicThetaInverseUnitIndex j))
    dsimp only [F]
    rw [hz,zero_mul]
  have hneg : F (-(d⁻¹))=
      ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3) := by
    dsimp only [F]
    rw [cubicThetaRamifiedTop_negative_inverse hh j]
    have he : h*omegaE^(j:ℕ)*((-(d⁻¹):Eisensteinˣ):Eisenstein)=-h := by
      rw [←hd,Units.val_neg,mul_neg,mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,mul_one]
    rw [he,cubicThetaArithmeticFourierResidue_neg (primary_ne_zero hh)]
  have hzero (e : Eisensteinˣ) (he : e≠d⁻¹) (he' : e≠-(d⁻¹)) : F e=0 := by
    have hunit : ¬(d*e=1 ∨ d*e=-1) := by
      rintro (hu | hu)
      · apply he
        calc e=d⁻¹*(d*e) := by group
             _=d⁻¹ := by rw [hu,mul_one]
      · apply he'
        calc e=d⁻¹*(d*e) := by group
             _=-(d⁻¹) := by rw [hu,mul_neg,mul_one]
    dsimp only [F]
    have hx : h*omegaE^(j:ℕ)*(e:Eisenstein)=h*((d*e:Eisensteinˣ):Eisenstein) := by
      rw [Units.val_mul,hd,mul_assoc]
    rw [hx,cubicThetaArithmeticFourierResidue_primary_unit hh,ite_eq_right hunit,mul_zero]
  have hp (e : Eisensteinˣ) : F e=if e=-(d⁻¹) then F (-(d⁻¹)) else 0 := by
    by_cases he : e=-(d⁻¹)
    · subst e
      exact (ite_eq_left rfl).symm
    · rw [ite_eq_right he]
      by_cases he' : e=d⁻¹
      · rw [he',hpos]
      · exact hzero e he' he
  change (∑' e : Eisensteinˣ, F e)=_
  rw [show (∑' e : Eisensteinˣ, F e)=∑' e : Eisensteinˣ,
      (if e=-(d⁻¹) then F (-(d⁻¹)) else 0) from tsum_congr hp,tsum_ite_eq]
  exact hneg

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedResidueFormula
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaObservationScaling

namespace OAI

/-! The explicit ramified residue solution in the normalized Whittaker
coefficient used by the Patterson theta expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedWhittaker_scale :
    (Complex.ofReal ((9:ℝ)^(-(1/3:ℝ))))*(3:ℂ)^(-(1/3:ℂ))=(1/3:ℂ) := by
  rw [Complex.ofReal_cpow (by norm_num)]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [show (9:ℂ)=((3:ℕ):ℂ)^2 by norm_num,←Complex.natCast_cpow_natCast_mul]
  norm_num only [Nat.cast_ofNat]
  rw [←Complex.cpow_add _ _ (by norm_num)]
  norm_num [Complex.cpow_neg,Complex.cpow_one]

theorem cubicThetaNormalizedObservedCoefficient_lambda_square_unit {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^2*(h*(e:Eisenstein)))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*cubicThetaNormalizedObservedCoefficient h := by
  have h0 := primary_ne_zero hh
  have hu : lambdaE^2*(e:Eisenstein)≠0 :=
    mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) e.ne_zero
  have hU : lambdaE^2*(h*(e:Eisenstein))=(lambdaE^2*(e:Eisenstein))*h := by ring
  have hN : norm (lambdaE^2*(e:Eisenstein))=9 := by
    rw [norm_mul_eq,norm_of_isUnit e.isUnit,mul_one,cubicThetaNorm_lambda_pow]
    norm_num
  have hw := cubicThetaPoleWeight_mul hu h0
  rw [hN] at hw
  have hR : cubicThetaArithmeticFourierResidue ((lambdaE^2*(e:Eisenstein))*h) (4/3)=
      (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3)) := by
    rw [←hU]
    exact cubicThetaArithmeticFourierResidue_lambda_square_unit hh e
  let K : ℂ := cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  have hL : cubicThetaNormalizedObservedCoefficient (lambdaE^2*(h*(e:Eisenstein)))=
      K*((Complex.ofReal ((9:ℝ)^(-(1/3:ℝ))))*(3:ℂ)^(-(1/3:ℂ)))*
        cubicThetaNinePhase ((e:Eisenstein)^2*h)*cubicThetaArithmeticFourierResidue h (4/3) := by
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    rw [hU,hw,hR]
    dsimp only [K]
    push_cast
    ring
  have hB : cubicThetaNormalizedObservedCoefficient h=K*cubicThetaArithmeticFourierResidue h (4/3) := by
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    dsimp only [K]
    ring
  rw [hL,hB,cubicThetaRamifiedWhittaker_scale]
  ring

theorem cubicThetaNormalizedObservedCoefficient_lambda_square {h : Eisenstein} (hh : primary h) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^2*h)=
      (1/3:ℂ)*cubicThetaNinePhase h*cubicThetaNormalizedObservedCoefficient h := by
  simpa only [Units.val_one,one_pow,mul_one,one_mul] using
    cubicThetaNormalizedObservedCoefficient_lambda_square_unit hh (1:Eisensteinˣ)

end CubicFirstMoment

end

end OAI

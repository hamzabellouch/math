import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNinePhase

namespace OAI

/-! The modulus-nine phase aligns the two surviving middle-row terms
on each of the three positive unit representatives. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNinePhase_middle_first {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaNinePhase (-omegaE^2*lambdaE*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*omegaE)^2*h)=
        cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  rw [←cubicThetaNinePhase_add]
  apply cubicThetaNinePhase_eq_of_difference hh ((j:ℕ)-1:ℤ)
  fin_cases j
  · norm_num only [Fin.val_zero,Nat.cast_zero,zero_sub,pow_zero,one_mul]
    dsimp only [lambdaE]
    linear_combination (2-2*omegaE)*h*omegaE_quadratic
  · norm_num only [Fin.val_one,Nat.cast_one,sub_self,pow_one,zero_mul]
    dsimp only [lambdaE]
    linear_combination -(omegaE^2)*h*omegaE_quadratic
  · norm_num only [Fin.val_two,Nat.cast_ofNat,Int.reduceSub,one_mul]
    dsimp only [lambdaE]
    linear_combination (omegaE^4-3*omegaE^3+3*omegaE-3)*h*omegaE_quadratic

theorem cubicThetaNinePhase_middle_second {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaNinePhase (omegaE*lambdaE*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(-omegaE^2))^2*h)=
        cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  rw [←cubicThetaNinePhase_add]
  apply cubicThetaNinePhase_eq_of_difference hh (if j=0 then -1 else if j=1 then 1 else 0)
  fin_cases j
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE+2)*h*omegaE_quadratic
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^4-omegaE^3+3*omegaE-3)*h*omegaE_quadratic
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^6-omegaE^5+omegaE^3)*h*omegaE_quadratic

end CubicFirstMoment

end

end OAI

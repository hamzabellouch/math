import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSquarefreeResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCoefficients

namespace OAI

/-! Complete primary squarefree/cube coefficient identification, up to
the actual scalar base residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_primary_cube {d : Eisenstein}
    (hd : primary d) (h : Eisenstein) (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (d^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  revert h
  refine primary_induction (P:=fun d => ∀ h : Eisenstein, h≠0 →
    cubicThetaArithmeticFourierResidue (d^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3)) ?_ ?_ hd
  · intro h _
    simp only [one_pow,one_mul]
  · intro p d hp hd ih h hh
    rw [show (p*d)^3*h=p^3*(d^3*h) by ring,
      cubicThetaArithmeticFourierResidue_cube hp (d^3*h)
        (mul_ne_zero (pow_ne_zero 3 (primary_ne_zero hd)) hh)]
    exact ih h hh

theorem cubicThetaWeightedFourierResidue_primary_cube {d : Eisenstein}
    (hd : primary d) (h : Eisenstein) (hh : h≠0) :
    cubicThetaWeightedFourierResidue (d^3*h)=
      (norm d:ℂ)⁻¹*cubicThetaWeightedFourierResidue h := by
  unfold cubicThetaWeightedFourierResidue
  rw [norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg (d^3)) (norm_nonneg h),
    cubicThetaNorm_cube_cpow,cubicThetaArithmeticFourierResidue_primary_cube hd h hh]
  ring

theorem cubicThetaWeightedFourierResidue_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaWeightedFourierResidue (c*d^3)=
      star (gauss c)/((Real.sqrt (norm c):ℂ)*(norm d:ℂ))*
        cubicThetaWeightedFourierResidue 1 := by
  rw [mul_comm c (d^3),cubicThetaWeightedFourierResidue_primary_cube hd c (primary_ne_zero hc),
    cubicThetaWeightedFourierResidue_squarefree hc hs]
  ring

theorem cubicThetaWeightedFourierResidue_theta_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaWeightedFourierResidue (c*d^3)=
      (cubicThetaArithmeticCoefficient (lambdaE*c*d^3)/81)*
        cubicThetaWeightedFourierResidue 1 := by
  rw [cubicThetaWeightedFourierResidue_primary hc hd hs,
    cubicThetaArithmeticCoefficient_primary hc hd hs]
  push_cast
  ring

end CubicFirstMoment

end

end OAI

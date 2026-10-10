import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitPhaseSymbol
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryPowerCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCoefficients
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven

namespace OAI

/-! The literal arithmetic theta coefficients obey the same exact
ramified phase relation as the actual normalized residue. Zero support is retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSymbol_cube_lower {d : Eisenstein} (hd : primary d)
    {v : Eisenstein} (hv : IsCoprime d v) : cubicSymbol (d^3) v=1 := by
  rw [show d^3=d*d*d by ring,cubicSymbol_mul_lower
    (mul_ne_zero (primary_ne_zero hd) (primary_ne_zero hd)) (primary_ne_zero hd),
    cubicSymbol_mul_lower (primary_ne_zero hd) (primary_ne_zero hd)]
  convert cubicSymbol_cube_of_isCoprime hd v hv using 1
  ring

lemma cubicThetaSymbol_primary_cube_part {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (e : Eisensteinˣ) :
    cubicSymbol (c*d^3) ((e:Eisenstein)^4*lambdaE^2)=
      cubicSymbol c ((e:Eisenstein)^4*lambdaE^2) := by
  have hv : IsCoprime d ((e:Eisenstein)^4*lambdaE^2) :=
    (isCoprime_mul_unit_left_right (e.isUnit.pow 4) d (lambdaE^2)).mpr
      (primary_coprime_lambda hd).pow_right
  rw [cubicSymbol_mul_lower (primary_ne_zero hc) (pow_ne_zero 3 (primary_ne_zero hd)),
    cubicThetaSymbol_cube_lower hd hv,mul_one]

theorem cubicThetaArithmeticCoefficient_ramified_parts {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^3*(c*d^3))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*(c*d^3))*
        cubicThetaArithmeticCoefficient (lambdaE*(c*d^3)) := by
  let R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^3*(c*d^3)) := {
    unit := e
    order := 3
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := rfl }
  have hp : primary (c*d^3) := primary_mul hc (by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul hd (primary_mul hd hd))
  rw [cubicThetaArithmeticCoefficient_formula R,
    cubicThetaNinePhase_unit_primary hp,cubicThetaSymbol_primary_cube_part hc hd,
    show lambdaE*(c*d^3)=lambdaE*c*d^3 by ring,
    cubicThetaArithmeticCoefficient_primary hc hd hs]
  norm_num [R,CubicThetaCoordinates.coefficient,CubicThetaCoordinates.amplitude,
    cubicThetaTwistedGauss,star_mul]
  ring

theorem cubicThetaArithmeticCoefficient_ramified_primary {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^3*h)=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticCoefficient (lambdaE*h) := by
  classical
  by_cases hR : Nonempty (CubicThetaCoordinates ((1:Eisenstein)*lambdaE^1*h))
  · obtain ⟨c,d,hc,hd,hs,he⟩ := (cubicThetaCoordinates_primary_power_iff hh 1 1).mp hR
    rw [he]
    exact cubicThetaArithmeticCoefficient_ramified_parts hc hd hs e
  · have hL : ¬Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^3*h)) :=
      mt (cubicThetaCoordinates_primary_support_iff hh e 1 3 1).mp hR
    have hB : ¬Nonempty (CubicThetaCoordinates (lambdaE*h)) := by
      simpa only [one_mul,pow_one] using hR
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hL,dite_eq_right hB,mul_zero]

theorem cubicThetaArithmeticCoefficient_ramified_signed {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^2*(h*(e:Eisenstein))))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [show -lambdaE*(lambdaE^2*(h*(e:Eisenstein)))=
    -((e:Eisenstein)*lambdaE^3*h) by ring,
    cubicThetaArithmeticCoefficient_even,cubicThetaArithmeticCoefficient_ramified_primary hh,
    neg_mul,cubicThetaArithmeticCoefficient_even]

end CubicFirstMoment

end

end OAI

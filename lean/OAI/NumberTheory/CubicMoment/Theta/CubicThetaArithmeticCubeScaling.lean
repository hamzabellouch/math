import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! Cube multiplication in the literal Patterson coefficient formula,
including its unit and ramified cases. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaCoordinates.mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    CubicThetaCoordinates (n*e^3) where
  unit := R.unit
  order := R.order
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart*e
  squarefree_primary := R.squarefree_primary
  cube_primary := primary_mul R.cube_primary he
  squarefree := R.squarefree
  numerator_eq := by
    calc
      n*e^3 = ((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3))*e^3 :=
        congrArg (fun x => x*e^3) R.numerator_eq
      _ = _ := by ring

lemma CubicThetaCoordinates.amplitude_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).amplitude=R.amplitude/norm e := by
  change 3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm (R.cubePart*e))=
    (3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm R.cubePart))/norm e
  rw [norm_mul_eq,div_div]
  congr 1
  ring

lemma CubicThetaCoordinates.coefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).coefficient=(norm e:ℂ)⁻¹*R.coefficient := by
  unfold coefficient
  rw [R.amplitude_mulPrimaryCube]
  dsimp only [mulPrimaryCube]
  push_cast
  split_ifs <;> ring

theorem cubicThetaArithmeticCoefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    cubicThetaArithmeticCoefficient (n*e^3)=(norm e:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  rw [cubicThetaArithmeticCoefficient_formula (R.mulPrimaryCube e he),
    cubicThetaArithmeticCoefficient_formula R,R.coefficient_mulPrimaryCube]

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCoefficients

namespace OAI

/-! The evenness of the cubic theta coefficients, derived directly from
all cases of the arithmetic formula, and the resulting horizontal symmetry. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaCoordinates.neg {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (-n) where
  unit := -R.unit
  order := R.order
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    calc
      _ = -((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3)) :=
        congrArg Neg.neg R.numerator_eq
      _ = _ := by simp

lemma CubicThetaCoordinates.neg_coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.neg.coefficient = R.coefficient := by
  have hu : ((-R.unit:Eisensteinˣ):Eisenstein)^4 = (R.unit:Eisenstein)^4 := by
    norm_num [Units.val_neg,neg_pow]
  have hs : ((-R.unit:Eisensteinˣ):Eisenstein) = 1 ∨
      ((-R.unit:Eisensteinˣ):Eisenstein) = -1 ↔
      (R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1 := by
    simp only [Units.val_neg,neg_eq_iff_eq_neg,neg_neg,or_comm]
  unfold coefficient cubicThetaUnitPhase
  simp only [neg,hu,hs,amplitude]

lemma cubicThetaArithmeticCoefficient_even (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (-n) = cubicThetaArithmeticCoefficient n := by
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hn
    rw [cubicThetaArithmeticCoefficient_formula R.neg,cubicThetaArithmeticCoefficient_formula R,
      R.neg_coefficient]
  · have hneg : ¬Nonempty (CubicThetaCoordinates (-n)) := by
      rintro ⟨R⟩
      apply hn
      simpa only [neg_neg] using (show Nonempty (CubicThetaCoordinates (-(-n))) from ⟨R.neg⟩)
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hneg]

lemma cubicThetaArithmetic_term_reflection (z : ℂ) (v : ℝ) (n : Eisenstein) :
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v (-n) =
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient (-z) v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    simp only [cubicThetaSeriesTerm,hn,hneg,ite_false,cubicThetaArithmeticCoefficient_even]
    have hf : cubicThetaFrequency (-n) = -cubicThetaFrequency n := by
      simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div]
    have hpair : tracePair (-cubicThetaFrequency n) z = tracePair (cubicThetaFrequency n) (-z) := by
      unfold tracePair
      rw [neg_mul,mul_neg]
    rw [hf,norm_neg,hpair]

/-- The series, as well as its arithmetic coefficients, is even. -/
theorem cubicThetaArithmetic_even (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (-z,v) =
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  unfold cubicThetaNonconstant
  rw [←(Equiv.neg Eisenstein).tsum_eq (fun n =>
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n)]
  apply tsum_congr
  intro n
  exact (cubicThetaArithmetic_term_reflection z v n).symm

end CubicFirstMoment

end

end OAI

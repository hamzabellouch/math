import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBaseScalarNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBaseScalarReal

namespace OAI

/-! The only remaining normalization ambiguity is the sign of the actual
base coefficient. No choice of that sign is made here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticBaseScalar_sq : cubicThetaArithmeticBaseScalar^2=1 := by
  calc
    _ = star cubicThetaArithmeticBaseScalar*cubicThetaArithmeticBaseScalar := by
      rw [cubicThetaArithmeticBaseScalar_star]
      ring
    _ = (‖cubicThetaArithmeticBaseScalar‖:ℂ)^2 := by
      simpa only [Complex.star_def] using Complex.conj_mul' cubicThetaArithmeticBaseScalar
    _ = 1 := by rw [cubicThetaArithmeticBaseScalar_norm]; norm_num

theorem cubicThetaArithmeticBaseScalar_sign :
    cubicThetaArithmeticBaseScalar=1 ∨ cubicThetaArithmeticBaseScalar= -1 := by
  have h : (cubicThetaArithmeticBaseScalar-1)*(cubicThetaArithmeticBaseScalar+1)=0 := by
    linear_combination cubicThetaArithmeticBaseScalar_sq
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

end CubicFirstMoment

end

end OAI

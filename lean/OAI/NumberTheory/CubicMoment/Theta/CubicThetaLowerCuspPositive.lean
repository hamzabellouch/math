import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLowerCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedPositiveSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedSeries

namespace OAI

/-! The two actual lower cusp expansions on the common frequency lattice,
valid throughout positive upper half-space. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaLowerCusp_positive (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaArithmeticBaseScalar*
        cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient (-n)) (z,v) := by
  have he := cubicThetaArithmeticModel_lowerCusp ((m:Eisenstein)+n*omegaE)
    (⟨(z,v),hv⟩ : CubicThetaPoint)
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE))) (z,v))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion (-((m:Eisenstein)+n*omegaE)))) (z,v)) at he
  have hb : -((m:Eisenstein)+n*omegaE)=((-m:ℤ):Eisenstein)+(-n:ℤ)*omegaE := by
    push_cast
    ring
  rw [hb] at he
  exact he.trans (cubicThetaShiftedPositiveSeries_common (-m) (-n) (by simpa using hn) hv z)

theorem cubicThetaLowerCusp_tenth_positive {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp omegaE)) (z,v))=
      cubicThetaArithmeticBaseScalar*
        cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient (-1)) (z,v) := by
  simpa only [Int.cast_zero,zero_add,Int.cast_one,one_mul] using
    cubicThetaLowerCusp_positive 0 1 (by norm_num) hv z

theorem cubicThetaLowerCusp_nineteenth_positive {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp (omegaE^2))) (z,v))=
      cubicThetaArithmeticBaseScalar*
        cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient 1) (z,v) := by
  have hb : ((-1:ℤ):Eisenstein)+(-1:ℤ)*omegaE=omegaE^2 := by
    push_cast
    linear_combination -omegaE_quadratic
  simpa only [hb,neg_neg] using cubicThetaLowerCusp_positive (-1) (-1) (by norm_num) hv z

theorem cubicThetaNormalizedSeries_lowerCusp (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE) • p)=
      cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient (-n)) p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE))) p.val)=_
  rw [cubicThetaLowerCusp_positive m n hn p.property p.val.1,←mul_assoc,
    inv_mul_cancel₀ cubicThetaArithmeticBaseScalar_ne_zero,one_mul]

end CubicFirstMoment

end

end OAI

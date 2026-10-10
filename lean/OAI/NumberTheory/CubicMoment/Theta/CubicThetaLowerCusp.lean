import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedSeriesIdentity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelInversion

namespace OAI

/-! The actual lower-unipotent representatives of the two nontrivial
cusps, obtained from the proved inversion symmetry. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaLowerCusp (b : Eisenstein) : SL(2,Eisenstein) :=
  cubicThetaFullInversion⁻¹*cubicThetaShiftedInversion (-b)

lemma cubicThetaLowerCusp_matrix (b : Eisenstein) :
    (cubicThetaLowerCusp b).val=!![1,0;b,1] := by
  have hi : (cubicThetaFullInversion⁻¹:SL(2,Eisenstein)).val=!![0,1;-1,0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [cubicThetaFullInversion,Matrix.adjugate_fin_two]
  change (cubicThetaFullInversion⁻¹).val*(cubicThetaShiftedInversion (-b)).val=_
  rw [hi]
  change (!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*!![-b,-1;1,0]=_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaArithmeticModel_inverseInversion (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion⁻¹ • p).val=
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have he := cubicThetaArithmeticModel_inversion (cubicThetaFullInversion⁻¹ • p)
  rw [smul_inv_smul] at he
  exact he.symm

lemma cubicThetaArithmeticModel_lowerCusp (b : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaLowerCusp b • p).val=
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaShiftedInversion (-b) • p).val := by
  rw [cubicThetaLowerCusp,mul_smul,cubicThetaArithmeticModel_inverseInversion]

theorem cubicThetaLowerCusp_series (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 1<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex
        (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE))) (z,v))=
      cubicThetaShiftedModelSeries (-n) z v := by
  have hv0 : 0<v := lt_trans (show (0:ℝ)<1 by norm_num) hv
  have he := cubicThetaArithmeticModel_lowerCusp ((m:Eisenstein)+n*omegaE)
    (⟨(z,v),hv0⟩ : CubicThetaPoint)
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp ((m:Eisenstein)+n*omegaE))) (z,v))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion (-((m:Eisenstein)+n*omegaE)))) (z,v)) at he
  have hb : -((m:Eisenstein)+n*omegaE)=((-m:ℤ):Eisenstein)+(-n:ℤ)*omegaE := by
    push_cast
    ring
  rw [hb] at he
  exact he.trans (cubicThetaShiftedSeriesIdentity (-m) (-n) (by simpa using hn) hv z)

lemma cubicThetaLowerCusp_tenth {v : ℝ} (hv : 1<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp omegaE)) (z,v))=
      cubicThetaShiftedModelSeries (-1) z v := by
  simpa only [Int.cast_zero,zero_add,Int.cast_one,one_mul] using
    cubicThetaLowerCusp_series 0 1 (by norm_num) hv z

lemma cubicThetaLowerCusp_nineteenth {v : ℝ} (hv : 1<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaLowerCusp (omegaE^2))) (z,v))=
      cubicThetaShiftedModelSeries 1 z v := by
  have hb : ((-1:ℤ):Eisenstein)+(-1:ℤ)*omegaE=omegaE^2 := by
    push_cast
    linear_combination -omegaE_quadratic
  simpa only [hb,neg_neg] using cubicThetaLowerCusp_series (-1) (-1) (by norm_num) hv z

end CubicFirstMoment

end

end OAI

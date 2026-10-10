import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedConstantCoefficient

namespace OAI

/-! The actual translated theta model has its proved nine-Eisenstein period. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaCuspTranslation_intertwines (b m : Eisenstein) :
    cubicThetaCuspTranslationMatrix b m*cubicThetaShiftedInversion b=
      cubicThetaShiftedInversion b*(cubicThetaPrincipalTranslation (3*m)).val := by
  apply Subtype.ext
  change (!![1-9*b*m,9*b^2*m;-9*m,1+9*b*m] : Matrix (Fin 2) (Fin 2) Eisenstein)*
      !![b,-1;1,0]=!![b,-1;1,0]*!![1,3*(3*m);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem cubicThetaShiftedModel_periodic (b m : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
        (p.val.1+9*(m:ℂ),p.val.2))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val) := by
  have he := cubicThetaArithmeticModel_automorphy (cubicThetaCuspTranslation b m)
    (cubicThetaShiftedInversion b • p)
  rw [cubicThetaCuspTranslation_value,one_mul] at he
  have ht : (cubicThetaCuspTranslation b m).val • (cubicThetaShiftedInversion b • p)=
      cubicThetaShiftedInversion b • ((cubicThetaPrincipalTranslation (3*m)).val • p) := by
    rw [←mul_smul,←mul_smul]
    change (cubicThetaCuspTranslationMatrix b m*cubicThetaShiftedInversion b) • p=_
    rw [cubicThetaCuspTranslation_intertwines]
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (((cubicThetaCuspTranslation b m).val • (cubicThetaShiftedInversion b • p)).val)=_ at he
  rw [ht,cubicThetaFullPointAction_apply] at he
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
      (cubicThetaPointCoordinates (cubicThetaPrincipalTranslation (3*m) • p)))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val) at he
  rw [cubicThetaPrincipalTranslation_coordinates] at he
  have hs : p.val.1+3*((3*m:Eisenstein):ℂ)=p.val.1+9*(m:ℂ) := by
    rw [Subalgebra.coe_mul,show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
    ring
  simpa only [cubicThetaPointCoordinates,hs] using he

end CubicFirstMoment

end

end OAI

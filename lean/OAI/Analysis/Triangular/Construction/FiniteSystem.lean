import OAI.Analysis.Triangular.Certificate.Inverse

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

lemma Uplus_equation : (1-R)*Uplus = Yf+R0*(gamma 1+gamma 0) := by
  unfold Uplus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.minusBlock_isUnit
lemma Uminus_equation : (1+R)*Uminus = Yf+R0*(gamma 1-gamma 0) := by
  unfold Uminus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.plusBlock_isUnit
lemma finiteSolution_equations :
    finiteSolution 0 = R*finiteSolution 1+R0*gamma 1+Yf ∧
    finiteSolution 1 = R*finiteSolution 0+R0*gamma 0 := by
  have hp := Uplus_equation
  have hm := Uminus_equation
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.one_mul,Matrix.mul_add,Matrix.mul_sub] at hp hm
  constructor
  · simp only [finiteSolution,Fin.val_zero,Fin.val_one,one_ne_zero,ite_true,ite_false,
      Matrix.mul_smul,Matrix.mul_sub]
    ext i j
    have hpij := congrFun (congrFun hp i) j
    have hmij := congrFun (congrFun hm i) j
    simp only [Matrix.add_apply,Matrix.sub_apply] at hpij hmij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    linarith
  · simp only [finiteSolution,Fin.val_zero,Fin.val_one,one_ne_zero,ite_true,ite_false,
      Matrix.mul_smul,Matrix.mul_add]
    ext i j
    have hpij := congrFun (congrFun hp i) j
    have hmij := congrFun (congrFun hm i) j
    simp only [Matrix.add_apply,Matrix.sub_apply] at hpij hmij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    linarith
end AtomicTriangular.Construction
end

end OAI

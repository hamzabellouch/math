import OAI.Combinatorics.PolynomialVacuum.Algebra.InhomogeneousCircuit

namespace OAI

namespace PolynomialVacuumAlgebra
namespace Inhomogeneous
open Classical
 

theorem cupRow_trace (N : ℕ) (X : ℕ → ℂ) (a : ℂ) (W : SpinTensor ℕ ℂ) (hW : DependsBefore N W) (s : ℕ → Spin) :
    cupRowCircuit N X a W (padCup N s)=
      exchangeDenominator (T*a) a * tracedTrain N (T*a) X W s := by
  have hX : skipOne 0 (frontFirstData X a)=X := by
    funext j; simp [skipOne,frontFirstData]
  have hv (ab : Pair) :
      braidTrain (T*a) (frontFirstData X a) 1 N (cupLinear 0 W)
        (natRotate (N+1) (replacePair (padCup N s) N (N+1) ab))=
      ∑ h : Spin,cup (ab.2,h)*
        braidTrain (T*a) X 0 N (auxiliaryInput h W) (insertOne N ab.1 s) := by
    rw [braidTrain_head_evaluate,rotate_padCup_head,hX,cup_headFiber,map_sum]
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply braidTrain_depends (auxiliaryInput_depends hW h) (by omega)
    exact rotate_padCup_tail N s ab
  simp only [cupRowCircuit,siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    padCup_left,padCup_right,numerator_cup_zero,rotateTensor,
    replacePair_right,hv,tracedTrain,mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using cup_trace_identity (fun h b =>
    braidTrain (T*a) X 0 N (auxiliaryInput h W) (insertOne N b s))

theorem spectralVector_depends (N : ℕ) (X : ℕ → ℂ) : DependsBefore N (spectralVector N X) := by
  intro s r h
  unfold spectralVector liftState liftPolyTensor
  congr 2
  funext j
  exact h j.val j.isLt

theorem front_trainDenominator (N : ℕ) (X : ℕ → ℂ) (a : ℂ) :
    trainDenominator (T*a) (frontFirstData X a) 1 N=trainDenominator (T*a) X 0 N := by
  have hh : ∀ k, trainDenominator (T*a) (frontFirstData X a) (k+1) N=
      trainDenominator (T*a) X k N := by
    induction N with
    | zero => intros; rfl
    | succ N ih =>
      intro k
      simp [trainDenominator,frontFirstData,ih]
  exact hh 0

theorem polynomialVacuum_tracedRow (N : ℕ) (X : ℕ → ℂ) (a : ℂ)
    (hs : spectralFusion N X a≠0) (hd : exchangeDenominator (T*a) a≠0) :
    tracedTrain N (T*a) X (spectralVector N X)=
      trainDenominator (T*a) X 0 N • spectralVector N X := by
  funext s
  have he:=congrFun (polynomialVacuum_cupRow N X a hs) (padCup N s)
  rw [cupRow_trace N X a _ (spectralVector_depends N X),front_trainDenominator] at he
  simp only [Pi.smul_apply,smul_eq_mul,cupLinear,LinearMap.coe_mk,AddHom.coe_mk,
    padCup_left,padCup_right,padCup_skip,cup,charge,add_zero,mul_zero,ite_true,zpow_zero,one_mul] at he
  apply mul_left_cancel₀ hd
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using he
end Inhomogeneous
end PolynomialVacuumAlgebra

end OAI

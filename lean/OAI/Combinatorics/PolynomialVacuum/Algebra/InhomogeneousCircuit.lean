import OAI.Combinatorics.PolynomialVacuum.Algebra.RowEigenvector

namespace OAI

namespace PolynomialVacuumAlgebra
namespace Inhomogeneous
open Classical

noncomputable def spectralVector (N : ℕ) (X : ℕ → ℂ) : SpinTensor ℕ ℂ :=
  liftState (polynomialVacuum N) X

noncomputable def frontCupData (X : ℕ → ℂ) (a : ℂ) : ℕ → ℂ := fun j => if j=0 then a else if j=1 then T*a else X (j-2)
noncomputable def finalCupData (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : ℕ → ℂ := fun j => if j<N then X j else if j=N then a else if j=N+1 then T*a else X (j-2)
noncomputable def reversedFinalData (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : ℕ → ℂ := swapSite N (finalCupData N X a)
def frontFirstData (X : ℕ → ℂ) (a : ℂ) : ℕ → ℂ := fun j => if j=0 then a else X (j-1)

noncomputable def cupRowCircuit (N : ℕ) (X : ℕ → ℂ) (a : ℂ) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  siteR N (T*a) a (rotateTensor (N+1) (braidTrain (T*a) (frontFirstData X a) 1 N (cupLinear 0 W)))

noncomputable def spectralFusion (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : ℂ := (1+T)*a*fusionProduct a X N

@[simp] theorem frontCupData_zero (X : ℕ → ℂ) (a : ℂ) : frontCupData X a 0=a := by simp [frontCupData]
@[simp] theorem frontCupData_one (X : ℕ → ℂ) (a : ℂ) : frontCupData X a 1=T*a := by simp [frontCupData]
@[simp] theorem finalCupData_left (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : finalCupData N X a N=a := by simp [finalCupData]
@[simp] theorem finalCupData_right (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : finalCupData N X a (N+1)=T*a := by simp [finalCupData]

@[simp] theorem front_skip (X : ℕ → ℂ) (a : ℂ) : skipTwo 0 (frontCupData X a)=X := by
  funext j; simp [skipTwo,frontCupData]
@[simp] theorem final_skip (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : skipTwo N (finalCupData N X a)=X := by
  funext j
  simp only [skipTwo,finalCupData]
  split_ifs <;> first | rfl | omega

@[simp] theorem front_fusion (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : naturalFusion N 0 (frontCupData X a)=spectralFusion N X a := by
  simp only [naturalFusion,frontCupData_zero,front_skip]
  simp [fusionProduct,spectralFusion]
@[simp] theorem final_fusion (N : ℕ) (X : ℕ → ℂ) (a : ℂ) : naturalFusion N N (finalCupData N X a)=spectralFusion N X a := by
  simp [naturalFusion,final_skip,fusionProduct,spectralFusion]

theorem front_insert (X : ℕ → ℂ) (a : ℂ) : insertOne 1 (T*a) (frontFirstData X a)=frontCupData X a := by
  funext j
  simp only [insertOne,frontFirstData,frontCupData]
  split_ifs <;> first | rfl | omega

 

theorem final_insert_rotation (N : ℕ) (X : ℕ → ℂ) (a : ℂ) :
    liftState (polynomialVacuum (N+2)) (natRotate (N+1) (reversedFinalData N X a))=
    liftState (polynomialVacuum (N+2)) (insertOne (1+N) (T*a) (frontFirstData X a)) := by
  apply liftState_params_congr
  intro j hj
  simp only [natRotate,rotationIndex,Function.comp_apply,reversedFinalData,swapSite,
    Equiv.swap_apply_def,finalCupData,insertOne,frontFirstData]
  split_ifs <;> first | rfl | omega

theorem rotateTensor_smul (N : ℕ) (c : ℂ) (W : SpinTensor ℕ ℂ) :
    rotateTensor N (c • W)=c • rotateTensor N W := by
  funext s
  simp [rotateTensor,smul_eq_mul,mul_left_comm]

 

theorem polynomialVacuum_cupRow (N : ℕ) (X : ℕ → ℂ) (a : ℂ)
    (hs : spectralFusion N X a≠0) :
    cupRowCircuit N X a (spectralVector N X)=
      (exchangeDenominator (T*a) a * trainDenominator (T*a) (frontFirstData X a) 1 N) •
        cupLinear N (spectralVector N X) := by
  let Ψ := liftState (polynomialVacuum (N+2))
  have hf := (polynomialVacuum_at (N+2)).cups N rfl 0 (by omega) (frontCupData X a) (by simp)
  have hl := (polynomialVacuum_at (N+2)).cups N rfl N le_rfl (finalCupData N X a) (by simp)
  simp only [front_fusion,front_skip] at hf
  simp only [final_fusion,final_skip] at hl
  have htrain := braidTrain_exchange (polynomialVacuum_at (N+2)).regular.exchange
    (T*a) (frontFirstData X a) 1 N (by omega)
  rw [front_insert,hf,map_smul] at htrain
  have hcy := (polynomialVacuum_at (N+2)).cyclic (N+1) (by omega) (reversedFinalData N X a)
  change rotateTensor (N+1) (liftState (polynomialVacuum (N+2)) (natRotate (N+1) (reversedFinalData N X a)))=Ψ (reversedFinalData N X a) at hcy
  rw [final_insert_rotation] at hcy
  have hrot := congrArg (rotateTensor (N+1)) htrain
  rw [rotateTensor_smul,rotateTensor_smul,hcy] at hrot
  have hex := (polynomialVacuum_at (N+2)).regular.exchange N (by omega) (reversedFinalData N X a)
  have hrl : reversedFinalData N X a N=T*a := by simp [reversedFinalData]
  have hrr : reversedFinalData N X a (N+1)=a := by simp [reversedFinalData]
  rw [hrl,hrr,show swapSite N (reversedFinalData N X a)=finalCupData N X a from swapSite_twice N _,hl] at hex
  have he := congrArg (siteR N (T*a) a) hrot
  rw [map_smul,map_smul,hex,smul_smul,smul_smul] at he
  change spectralFusion N X a • cupRowCircuit N X a (spectralVector N X)=_ at he
  funext s
  apply mul_left_cancel₀ hs
  have he' := congrFun he s
  change spectralFusion N X a * cupRowCircuit N X a (spectralVector N X) s=
    (trainDenominator (T*a) (frontFirstData X a) 1 N * exchangeDenominator (T*a) a * spectralFusion N X a) *
      cupLinear N (spectralVector N X) s at he'
  change spectralFusion N X a * cupRowCircuit N X a (spectralVector N X) s=
    spectralFusion N X a * ((exchangeDenominator (T*a) a * trainDenominator (T*a) (frontFirstData X a) 1 N) * cupLinear N (spectralVector N X) s)
  rw [he']
  ring

end Inhomogeneous
end PolynomialVacuumAlgebra

end OAI

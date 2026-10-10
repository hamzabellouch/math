import OAI.Combinatorics.PolynomialVacuum.Algebra.AllSizeInduction

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def homogeneousVector (N : ℕ) : SpinTensor ℕ ℂ :=
  liftState (polynomialVacuum N) (fun _ => 1)

noncomputable def frontCupData (a : ℂ) : ℕ → ℂ := fun j => if j=0 then a else if j=1 then T*a else 1
noncomputable def finalCupData (N : ℕ) (a : ℂ) : ℕ → ℂ := fun j => if j=N then a else if j=N+1 then T*a else 1
noncomputable def reversedFinalData (N : ℕ) (a : ℂ) : ℕ → ℂ := swapSite N (finalCupData N a)
def frontFirstData (a : ℂ) : ℕ → ℂ := fun j => if j=0 then a else 1

noncomputable def cupRowCircuit (N : ℕ) (a : ℂ) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  siteR N (T*a) a (rotateTensor (N+1) (braidTrain (T*a) (frontFirstData a) 1 N (cupLinear 0 W)))

noncomputable def homogeneousFusion (N : ℕ) (a : ℂ) : ℂ := (1+T)*a*fusionPair a 1^N

@[simp] theorem frontCupData_zero (a : ℂ) : frontCupData a 0=a := by simp [frontCupData]
@[simp] theorem frontCupData_one (a : ℂ) : frontCupData a 1=T*a := by simp [frontCupData]
@[simp] theorem finalCupData_left (N : ℕ) (a : ℂ) : finalCupData N a N=a := by simp [finalCupData]
@[simp] theorem finalCupData_right (N : ℕ) (a : ℂ) : finalCupData N a (N+1)=T*a := by simp [finalCupData]

@[simp] theorem front_skip (a : ℂ) : skipTwo 0 (frontCupData a)=fun _ => 1 := by
  funext j; simp [skipTwo,frontCupData]
@[simp] theorem final_skip (N : ℕ) (a : ℂ) : skipTwo N (finalCupData N a)=fun _ => 1 := by
  funext j
  simp only [skipTwo,finalCupData]
  split_ifs <;> first | rfl | omega

@[simp] theorem front_fusion (N : ℕ) (a : ℂ) : naturalFusion N 0 (frontCupData a)=homogeneousFusion N a := by
  simp only [naturalFusion,frontCupData_zero,front_skip]
  simp [fusionProduct,homogeneousFusion]
@[simp] theorem final_fusion (N : ℕ) (a : ℂ) : naturalFusion N N (finalCupData N a)=homogeneousFusion N a := by
  simp [naturalFusion,final_skip,fusionProduct,homogeneousFusion]

theorem front_insert (a : ℂ) : insertOne 1 (T*a) (frontFirstData a)=frontCupData a := by
  funext j
  simp only [insertOne,frontFirstData,frontCupData]
  split_ifs <;> first | rfl | omega

 

theorem final_insert_rotation (N : ℕ) (a : ℂ) :
    liftState (polynomialVacuum (N+2)) (natRotate (N+1) (reversedFinalData N a))=
    liftState (polynomialVacuum (N+2)) (insertOne (1+N) (T*a) (frontFirstData a)) := by
  apply liftState_params_congr
  intro j hj
  simp only [natRotate,rotationIndex,Function.comp_apply,reversedFinalData,swapSite,
    Equiv.swap_apply_def,finalCupData,insertOne,frontFirstData]
  split_ifs <;> first | rfl | omega

theorem rotateTensor_smul (N : ℕ) (c : ℂ) (W : SpinTensor ℕ ℂ) :
    rotateTensor N (c • W)=c • rotateTensor N W := by
  funext s
  simp [rotateTensor,smul_eq_mul,mul_left_comm]

 

theorem polynomialVacuum_cupRow (N : ℕ) (a : ℂ)
    (hs : homogeneousFusion N a≠0) :
    cupRowCircuit N a (homogeneousVector N)=
      (exchangeDenominator (T*a) a * trainDenominator (T*a) (frontFirstData a) 1 N) •
        cupLinear N (homogeneousVector N) := by
  let Ψ := liftState (polynomialVacuum (N+2))
  have hf := (polynomialVacuum_at (N+2)).cups N rfl 0 (by omega) (frontCupData a) (by simp)
  have hl := (polynomialVacuum_at (N+2)).cups N rfl N le_rfl (finalCupData N a) (by simp)
  simp only [front_fusion,front_skip] at hf
  simp only [final_fusion,final_skip] at hl
  have htrain := braidTrain_exchange (polynomialVacuum_at (N+2)).regular.exchange
    (T*a) (frontFirstData a) 1 N (by omega)
  rw [front_insert,hf,map_smul] at htrain
  have hcy := (polynomialVacuum_at (N+2)).cyclic (N+1) (by omega) (reversedFinalData N a)
  change rotateTensor (N+1) (liftState (polynomialVacuum (N+2)) (natRotate (N+1) (reversedFinalData N a)))=Ψ (reversedFinalData N a) at hcy
  rw [final_insert_rotation] at hcy
  have hrot := congrArg (rotateTensor (N+1)) htrain
  rw [rotateTensor_smul,rotateTensor_smul,hcy] at hrot
  have hex := (polynomialVacuum_at (N+2)).regular.exchange N (by omega) (reversedFinalData N a)
  have hrl : reversedFinalData N a N=T*a := by simp [reversedFinalData]
  have hrr : reversedFinalData N a (N+1)=a := by simp [reversedFinalData]
  rw [hrl,hrr,show swapSite N (reversedFinalData N a)=finalCupData N a from swapSite_twice N _,hl] at hex
  have he := congrArg (siteR N (T*a) a) hrot
  rw [map_smul,map_smul,hex,smul_smul,smul_smul] at he
  change homogeneousFusion N a • cupRowCircuit N a (homogeneousVector N)=_ at he
  funext s
  apply mul_left_cancel₀ hs
  have he' := congrFun he s
  change homogeneousFusion N a * cupRowCircuit N a (homogeneousVector N) s=
    (trainDenominator (T*a) (frontFirstData a) 1 N * exchangeDenominator (T*a) a * homogeneousFusion N a) *
      cupLinear N (homogeneousVector N) s at he'
  change homogeneousFusion N a * cupRowCircuit N a (homogeneousVector N) s=
    homogeneousFusion N a * ((exchangeDenominator (T*a) a * trainDenominator (T*a) (frontFirstData a) 1 N) * cupLinear N (homogeneousVector N) s)
  rw [he']
  ring

end PolynomialVacuumAlgebra

end OAI

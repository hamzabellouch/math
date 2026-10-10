import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic

namespace OAI

noncomputable section

namespace KKMatrixQuantization

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] [StarRing A]

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A)

theorem matrixAverage_cycle_unit (x : A) (k l : ι) :
    matrixAverage ρ (matrixUnit ρ k l*x)=matrixAverage ρ (x*matrixUnit ρ k l) := by
  change (Fintype.card ι:ℂ)⁻¹ • (∑ i,∑ j,matrixUnit ρ i j*(matrixUnit ρ k l*x)*matrixUnit ρ j i)=
    (Fintype.card ι:ℂ)⁻¹ • (∑ i,∑ j,matrixUnit ρ i j*(x*matrixUnit ρ k l)*matrixUnit ρ j i)
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs => arg 2; intro j; rw [← mul_assoc,matrixUnit_mul]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  conv_rhs => arg 2; intro j; rw [mul_assoc,mul_assoc,matrixUnit_mul]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,mul_assoc]

theorem matrixAverage_sum {κ : Type*} (s : Finset κ) (f : κ → A) :
    matrixAverage ρ (∑ i∈s, f i)=∑ i∈s, matrixAverage ρ (f i) :=
  map_sum (matrixAverageLinear ρ) f s

theorem matrixAverage_cycle (a : Matrix ι ι ℂ) (x : A) :
    matrixAverage ρ (ρ a*x)=matrixAverage ρ (x*ρ a) := by
  rw [matrix_representation ρ a]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,matrixAverage_sum,
    matrixAverage_smul,matrixAverage_cycle_unit]

theorem matrixAverage_conjugate (a : unitary (Matrix ι ι ℂ)) (x : A) :
    matrixAverage ρ (ρ a.val*x*ρ (star a.val))=matrixAverage ρ x := by
  rw [mul_assoc,matrixAverage_cycle,mul_assoc,← map_mul,Unitary.coe_star_mul_self,map_one,mul_one]

end

end KKMatrixQuantization
end

end OAI

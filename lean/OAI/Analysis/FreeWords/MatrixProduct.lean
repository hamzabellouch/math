import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic
import OAI.Analysis.FreeWords.MatrixUnitHom

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKProjectionSupport

noncomputable section

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (σ : Matrix κ κ ℂ →⋆ₐ[ℂ] A)

variable (hc : ∀ i j k l, Commute (matrixUnit ρ i j) (matrixUnit σ k l))

def productUnits (a b : ι × κ) := matrixUnit ρ a.1 b.1*matrixUnit σ a.2 b.2

omit [StarModule ℂ A] in
include hc in
theorem productUnits_mul (a b c d : ι × κ) :
    productUnits ρ σ a b*productUnits ρ σ c d=if b=c then productUnits ρ σ a d else 0 := by
  dsimp only [productUnits]
  rw [(hc c.1 d.1 a.2 b.2).symm.mul_mul_mul_comm _ _,matrixUnit_mul,matrixUnit_mul]
  by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2
  · have hh : b=c := Prod.ext h1 h2
    simp only [ite_eq_left h1,ite_eq_left h2,ite_eq_left hh]
  · have hh : b≠c := fun h => h2 (congrArg Prod.snd h)
    simp only [ite_eq_left h1,ite_eq_right h2,ite_eq_right hh,mul_zero]
  · have hh : b≠c := fun h => h1 (congrArg Prod.fst h)
    simp only [ite_eq_right h1,ite_eq_left h2,ite_eq_right hh,zero_mul]
  · have hh : b≠c := fun h => h1 (congrArg Prod.fst h)
    simp only [ite_eq_right h1,ite_eq_right h2,ite_eq_right hh,zero_mul]

omit [StarModule ℂ A] in
theorem productUnits_one : (∑ i : ι × κ, productUnits ρ σ i i)=1 := by
  simp only [productUnits,Fintype.sum_prod_type,← Finset.mul_sum,matrixUnit_sum_diag,mul_one]

omit [StarModule ℂ A] in
include hc in
theorem productUnits_star (a b : ι × κ) : star (productUnits ρ σ a b)=productUnits ρ σ b a := by
  simp only [productUnits,star_mul,matrixUnit_star]
  exact (hc b.1 a.1 b.2 a.2).eq.symm

def matrixProduct : Matrix (ι × κ) (ι × κ) ℂ →⋆ₐ[ℂ] A :=
  matrixUnitHom (productUnits ρ σ) (productUnits_mul ρ σ hc) (productUnits_one ρ σ)
    (productUnits_star ρ σ hc)

@[simp] theorem matrixProduct_unit (a b : ι × κ) :
    matrixUnit (matrixProduct ρ σ hc) a b=productUnits ρ σ a b := by
  change (∑ i, ∑ j, Matrix.single a b (1:ℂ) i j • productUnits ρ σ i j)=_
  simp only [Matrix.single_apply,ite_and,ite_smul,zero_smul,one_smul,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem matrixProduct_average (x : A) :
    matrixAverage (matrixProduct ρ σ hc) x=matrixAverage σ (matrixAverage ρ x) := by
  change (Fintype.card (ι × κ):ℂ)⁻¹ • (∑ a,∑ b,matrixUnit (matrixProduct ρ σ hc) a b*x*
    matrixUnit (matrixProduct ρ σ hc) b a)=_
  simp only [matrixProduct_unit,productUnits,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type]
  change ((Fintype.card κ:ℂ)⁻¹*(Fintype.card ι:ℂ)⁻¹) •
    (∑ i,∑ k,∑ j,∑ l,(matrixUnit ρ i j*matrixUnit σ k l)*x*(matrixUnit ρ j i*matrixUnit σ l k))=
    (Fintype.card κ:ℂ)⁻¹ • (∑ k,∑ l,matrixUnit σ k l*
      ((Fintype.card ι:ℂ)⁻¹ • (∑ i,∑ j,matrixUnit ρ i j*x*matrixUnit ρ j i))*matrixUnit σ l k)
  simp only [mul_smul_comm,smul_mul_assoc,← Finset.smul_sum,smul_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hc i j k l).eq]
  simp only [mul_assoc]

end

end KKMatrixQuantization
end

end OAI

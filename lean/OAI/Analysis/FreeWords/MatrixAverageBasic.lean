import Mathlib

namespace OAI

noncomputable section

namespace KKMatrixQuantization

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] [StarRing A]

def matrixAverage (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (x : A) : A :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, ∑ j,
    ρ (Matrix.single i j 1) * x * ρ (Matrix.single j i 1)

end

end KKMatrixQuantization

namespace KKMatrixQuantization

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] [StarRing A]

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A)

def matrixUnit (i j : ι) : A := ρ (Matrix.single i j 1)

@[simp] theorem matrixUnit_star (i j : ι) : star (matrixUnit ρ i j)=matrixUnit ρ j i := by
  simp only [matrixUnit,← map_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,star_one]

theorem matrixUnit_mul (i j k l : ι) :
    matrixUnit ρ i j*matrixUnit ρ k l=if j=k then matrixUnit ρ i l else 0 := by
  simp only [matrixUnit,← map_mul]
  split_ifs with h
  · subst k; simp only [Matrix.single_mul_single_same,one_mul]
  · rw [Matrix.single_mul_single_of_ne 1 i j k h 1,map_zero]

@[simp] theorem matrixUnit_mul_same (i j k : ι) :
    matrixUnit ρ i j*matrixUnit ρ j k=matrixUnit ρ i k := by
  rw [matrixUnit_mul,ite_eq_left rfl]

@[simp] theorem matrixUnit_sum_diag : (∑ i, matrixUnit ρ i i)=1 := by
  simp only [matrixUnit,← map_sum,Matrix.sum_single_one,map_one]

theorem matrix_representation (x : Matrix ι ι ℂ) : ρ x=∑ i, ∑ j, x i j • matrixUnit ρ i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum,matrixUnit]
  congr 1; ext i
  congr 1; ext j
  rw [← map_smul,Matrix.smul_single,smul_eq_mul,mul_one]

theorem matrixAverage_add (x y : A) : matrixAverage ρ (x+y)=matrixAverage ρ x+matrixAverage ρ y := by
  simp only [matrixAverage,mul_add,add_mul,Finset.sum_add_distrib,smul_add]

theorem matrixAverage_smul (c : ℂ) (x : A) : matrixAverage ρ (c • x)=c • matrixAverage ρ x := by
  simp only [matrixAverage,mul_smul_comm,smul_mul_assoc,← Finset.smul_sum]
  rw [smul_comm]

def matrixAverageLinear : A →ₗ[ℂ] A where
  toFun := matrixAverage ρ
  map_add' := matrixAverage_add ρ
  map_smul' := fun c x => by exact matrixAverage_smul ρ c x

theorem matrixAverage_commute (x : A) (k l : ι) :
    Commute (matrixAverage ρ x) (matrixUnit ρ k l) := by
  change matrixAverage ρ x*matrixUnit ρ k l=matrixUnit ρ k l*matrixAverage ρ x
  change ((Fintype.card ι:ℂ)⁻¹ • (∑ i, ∑ j, matrixUnit ρ i j*x*matrixUnit ρ j i))*matrixUnit ρ k l=
    matrixUnit ρ k l*((Fintype.card ι:ℂ)⁻¹ • (∑ i, ∑ j, matrixUnit ρ i j*x*matrixUnit ρ j i))
  simp only [smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]
  congr 1
  calc
    (∑ i, ∑ j, matrixUnit ρ i j*x*matrixUnit ρ j i*matrixUnit ρ k l) =
      ∑ j, matrixUnit ρ k j*x*matrixUnit ρ j l := by
        simp only [mul_assoc,matrixUnit_mul,mul_ite,mul_zero,Finset.sum_ite_irrel,
          Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = ∑ i, ∑ j, matrixUnit ρ k l*(matrixUnit ρ i j*x*matrixUnit ρ j i) := by
      symm
      simp only [← mul_assoc,matrixUnit_mul,ite_mul,zero_mul,Finset.sum_ite_irrel,
        Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem matrixAverage_fixed [Nonempty ι] (x : A)
    (hx : ∀ i j, Commute x (matrixUnit ρ i j)) : matrixAverage ρ x=x := by
  have hc : (Fintype.card ι:ℂ)≠0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  change (Fintype.card ι:ℂ)⁻¹ • (∑ i, ∑ j, matrixUnit ρ i j*x*matrixUnit ρ j i)=x
  have he (i j : ι) : matrixUnit ρ i j*x*matrixUnit ρ j i=matrixUnit ρ i i*x := by
    rw [mul_assoc,(hx j i).eq,← mul_assoc,matrixUnit_mul_same]
  simp only [he,Finset.sum_const,Finset.card_univ,← Finset.smul_sum,matrixUnit_sum_diag,
    ← Finset.sum_mul,one_mul]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ hc,one_smul]

theorem matrixAverage_idempotent [Nonempty ι] (x : A) :
    matrixAverage ρ (matrixAverage ρ x)=matrixAverage ρ x :=
  matrixAverage_fixed ρ _ (matrixAverage_commute ρ x)

end

end KKMatrixQuantization
end

end OAI

import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic

namespace OAI

noncomputable section

namespace KKMatrixQuantization

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] [StarRing A]

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (o : ι)

def cornerLift (x : A) : A := ∑ i, matrixUnit ρ i o*x*matrixUnit ρ o i

theorem cornerLift_star (x : A) : star (cornerLift ρ o x)=cornerLift ρ o (star x) := by
  simp only [cornerLift,star_sum,star_mul,matrixUnit_star,mul_assoc]

theorem mul_cornerLift (x : A) (i j : ι) :
    matrixUnit ρ i j*cornerLift ρ o x=matrixUnit ρ i o*x*matrixUnit ρ o j := by
  simp only [cornerLift,Finset.mul_sum,← mul_assoc,matrixUnit_mul,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem cornerLift_mul (x : A) (i j : ι) :
    cornerLift ρ o x*matrixUnit ρ i j=matrixUnit ρ i o*x*matrixUnit ρ o j := by
  simp only [cornerLift,Finset.sum_mul,mul_assoc,matrixUnit_mul,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem cornerLift_commute (x : A) (i j : ι) : Commute (cornerLift ρ o x) (matrixUnit ρ i j) := by
  exact (cornerLift_mul ρ o x i j).trans (mul_cornerLift ρ o x i j).symm

theorem cornerLift_compression (x : A) :
    matrixUnit ρ o o*cornerLift ρ o x*matrixUnit ρ o o=matrixUnit ρ o o*x*matrixUnit ρ o o := by
  rw [mul_cornerLift,mul_assoc,matrixUnit_mul_same]

theorem cornerLift_one_corner : cornerLift ρ o (matrixUnit ρ o o)=1 := by
  simp only [cornerLift,matrixUnit_mul_same,matrixUnit_sum_diag]

theorem cornerLift_mul_cornerLift (x y : A) :
    cornerLift ρ o x*cornerLift ρ o y=cornerLift ρ o (x*matrixUnit ρ o o*y) := by
  simp only [cornerLift,Finset.sum_mul,Finset.mul_sum]
  simp only [mul_assoc]
  conv_lhs =>
    arg 2; intro i; arg 2; intro j
    rw [← mul_assoc (matrixUnit ρ o j) (matrixUnit ρ i o),matrixUnit_mul]
  simp only [ite_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem cornerLift_fixed (x : A) (hx : ∀ i j, Commute x (matrixUnit ρ i j)) :
    cornerLift ρ o (matrixUnit ρ o o*x*matrixUnit ρ o o)=x := by
  have he (i : ι) : matrixUnit ρ i o*(matrixUnit ρ o o*x*matrixUnit ρ o o)*matrixUnit ρ o i=
      matrixUnit ρ i i*x := by
    simp only [← mul_assoc,matrixUnit_mul_same]
    rw [mul_assoc,matrixUnit_mul_same,mul_assoc,(hx o i).eq,← mul_assoc,matrixUnit_mul_same]
  simp only [cornerLift,he,← Finset.sum_mul,matrixUnit_sum_diag,one_mul]

theorem matrix_corner_expansion (x : A) :
    x = ∑ i, ∑ j, matrixUnit ρ i o*cornerLift ρ o (matrixUnit ρ o i*x*matrixUnit ρ j o)*matrixUnit ρ o j := by
  have he (i j : ι) : matrixUnit ρ i o*cornerLift ρ o (matrixUnit ρ o i*x*matrixUnit ρ j o)*matrixUnit ρ o j=
      matrixUnit ρ i i*x*matrixUnit ρ j j := by
    rw [mul_cornerLift]
    simp only [← mul_assoc,matrixUnit_mul_same]
    simp only [mul_assoc,matrixUnit_mul_same]
  simp only [he,← Finset.mul_sum,matrixUnit_sum_diag,mul_one,← Finset.sum_mul,one_mul]

theorem commute_of_matrix_coordinates (x : A)
    (he : ∀ i j, Commute x (matrixUnit ρ i j))
    (hL : ∀ y, Commute x (cornerLift ρ o y)) (y : A) : Commute x y := by
  rw [matrix_corner_expansion ρ o y]
  apply Commute.sum_right
  intro i hi
  apply Commute.sum_right
  intro j hj
  exact ((he i o).mul_right (hL _)).mul_right (he o j)

end

end KKMatrixQuantization
end

end OAI

import OAI.Analysis.TriangularHilbert.RankJump

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowNorm_rowStar (A : Three → Matrix ι ι ℂ) (v : Three) (i : ι) :
    rowNorm (rowStar A v) (v,i) = Real.sqrt (∑ w, ∑ j, ‖triangleBlocks A v w i j‖^2) := by
  simp only [rowNorm,Fintype.sum_prod_type,rowStar_apply,ite_true]

lemma colNorm_rowStar (A : Three → Matrix ι ι ℂ) (v w : Three) (j : ι) :
    colNorm (rowStar A v) (w,j) = Real.sqrt (∑ i, ‖triangleBlocks A v w i j‖^2) := by
  unfold colNorm
  simp only [Fintype.sum_prod_type,rowStar_apply]
  congr 1
  have he (a : Three) : (∑ i, ‖if a = v then triangleBlocks A a w i j else 0‖^2) =
      if a = v then (∑ i, ‖triangleBlocks A a w i j‖^2) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  simp

lemma rowStar_norm_mono {A B : Three → Matrix ι ι ℂ}
    (h : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar A v a b‖ ≤ ‖rowStar B v a b‖ := by
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    unfold triangleBlocks
    split_ifs <;> first | exact le_rfl | exact h _ _ _ | simpa only [Matrix.conjTranspose_apply,norm_star] using h _ _ _
  · simp [hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖ = Real.sqrt (g v i)*‖A v i j‖*Real.sqrt (g (v+1) j) := by
  simp only [weightedArray,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_norm_sq (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) (i j : ι) :
    ‖weightedArray A g v i j‖^2 = g v i*‖A v i j‖^2*g (v+1) j := by
  rw [weightedArray_norm,mul_pow,mul_pow,Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]

lemma rowNorm_weightedStar_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (i : ι) :
    rowNorm (rowStar (weightedArray A g) 0) (0,i) =
      Real.sqrt (g 0 i) * Real.sqrt ((∑ j, ‖A 0 i j‖^2*g 1 j)+(∑ j, ‖A 2 j i‖^2*g 2 j)) := by
  rw [rowNorm_rowStar,Fin.sum_univ_three]
  simp only [triangleBlocks,show (0:Three) ≠ 1 by decide,show (1:Three) ≠ 0 by decide,show (2:Three) ≠ 0 by decide,show (2:Three) ≠ 1 by decide,ite_true,ite_false,Matrix.zero_apply,Matrix.conjTranspose_apply,norm_star,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add]
  simp_rw [weightedArray_norm_sq A g hg]
  simp only [show (0:Three)+1=1 by decide,show (2:Three)+1=0 by decide]
  have he : (∑ j, g 0 i*‖A 0 i j‖^2*g 1 j)+(∑ j, g 2 j*‖A 2 j i‖^2*g 0 i) =
      g 0 i*((∑ j, ‖A 0 i j‖^2*g 1 j)+(∑ j, ‖A 2 j i‖^2*g 2 j)) := by
    simp only [mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he,Real.sqrt_mul (hg 0 i)]

lemma colNorm_weightedStar_zero_one (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (j : ι) :
    colNorm (rowStar (weightedArray A g) 0) (1,j) =
      Real.sqrt (g 1 j) * Real.sqrt (∑ i, ‖A 0 i j‖^2*g 0 i) := by
  rw [colNorm_rowStar]
  simp only [triangleBlocks,show (0:Three) ≠ 1 by decide,show (1:Three) ≠ 0 by decide,ite_true,ite_false]
  simp_rw [weightedArray_norm_sq A g hg]
  rw [show (0:Three)+1=1 by decide]
  have he : (∑ i, g 0 i*‖A 0 i j‖^2*g 1 j) = g 1 j*(∑ i, ‖A 0 i j‖^2*g 0 i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,Real.sqrt_mul (hg 1 j)]

lemma rowNorm_weightedStar_one (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (j : ι) :
    rowNorm (rowStar (weightedArray A g) 1) (1,j) =
      Real.sqrt (g 1 j) * Real.sqrt ((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
  rw [rowNorm_rowStar,Fin.sum_univ_three]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,show (2:Three) ≠ 0 by decide,show (2:Three) ≠ 1 by decide,ite_true,ite_false,Matrix.zero_apply,Matrix.conjTranspose_apply,norm_star,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,add_zero]
  simp_rw [weightedArray_norm_sq A g hg]
  simp only [show (0:Three)+1=1 by decide,show (1:Three)+1=2 by decide]
  have he : (∑ i, g 0 i*‖A 0 i j‖^2*g 1 j)+(∑ i, g 1 j*‖A 1 j i‖^2*g 2 i) =
      g 1 j*((∑ i, ‖A 0 i j‖^2*g 0 i)+(∑ i, ‖A 1 j i‖^2*g 2 i)) := by
    simp only [mul_add,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he,Real.sqrt_mul (hg 1 j)]

lemma colNorm_weightedStar_one_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (i : ι) :
    colNorm (rowStar (weightedArray A g) 1) (0,i) =
      Real.sqrt (g 0 i) * Real.sqrt (∑ j, ‖A 0 i j‖^2*g 1 j) := by
  rw [colNorm_rowStar]
  simp only [triangleBlocks,show (1:Three) ≠ 0 by decide,ite_true,ite_false,Matrix.conjTranspose_apply,norm_star]
  simp_rw [weightedArray_norm_sq A g hg]
  rw [show (0:Three)+1=1 by decide]
  have he : (∑ j, g 0 i*‖A 0 i j‖^2*g 1 j) = g 0 i*(∑ j, ‖A 0 i j‖^2*g 1 j) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he,Real.sqrt_mul (hg 0 i)]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

import OAI.Analysis.TriangularHilbert.StarNorm

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
def replaceZero (A : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) : Three → Matrix ι ι ℂ :=
  fun v => if v = 0 then B else A v

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_sub (A B : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (A-B) g = weightedArray A g-weightedArray B g := by
  ext v i j
  simp [weightedArray,mul_sub,sub_mul]

lemma rowStar_sub (A B : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar (A-B) v = rowStar A v-rowStar B v := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply,Matrix.sub_apply]
  by_cases hv : a = v
  · simp only [ite_eq_left hv]
    fin_cases a <;> fin_cases b <;> simp [triangleBlocks]
  · simp only [ite_eq_right hv,sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma replaceZero_sub (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ) :
    replaceZero A B-replaceZero A C = replaceZero 0 (B-C) := by
  ext v i j
  by_cases hv : v=0 <;> simp [replaceZero,hv]

omit [Fintype ι] [DecidableEq ι] in
lemma weightedArray_replaceZero_zero (B : Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    weightedArray (replaceZero 0 B) g = replaceZero 0 (fun i j => (Real.sqrt (g 0 i):ℂ)*B i j*(Real.sqrt (g 1 j):ℂ)) := by
  ext v i j
  by_cases hv : v=0
  · subst v
    simp [weightedArray,replaceZero,show (0:Three)+1=1 by decide]
  · simp [weightedArray,replaceZero,hv]

lemma rowStar_replaceZero_two (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (g : Three → ι → ℝ) :
    rowStar (weightedArray (replaceZero A B) g) 2 = rowStar (weightedArray (replaceZero A C) g) 2 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply]
  by_cases ha : a=2
  · subst a
    simp only [ite_true]
    fin_cases b <;> simp [triangleBlocks,weightedArray,replaceZero]
  · simp [ha]

lemma jump_sum_zero (M : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    (∑ a, ∑ b, rowNorm (rowStar M 0) a*colNorm (rowStar M 0) b*‖rowStar (replaceZero 0 B) 0 a b‖) =
      ∑ i, ∑ j, rowNorm (rowStar M 0) (0,i)*colNorm (rowStar M 0) (1,j)*‖B i j‖ := by
  simp only [Fintype.sum_prod_type,rowStar_apply]
  simp [Fin.sum_univ_three,triangleBlocks,replaceZero]

lemma jump_sum_one (M : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    (∑ a, ∑ b, rowNorm (rowStar M 1) a*colNorm (rowStar M 1) b*‖rowStar (replaceZero 0 B) 1 a b‖) =
      ∑ i, ∑ j, rowNorm (rowStar M 1) (1,j)*colNorm (rowStar M 1) (0,i)*‖B i j‖ := by
  simp only [Fintype.sum_prod_type,rowStar_apply]
  simp only [Fin.sum_univ_three]
  simp only [show (1:Three) ≠ 0 by decide, show (2:Three) ≠ 1 by decide,show (0:Three) ≠ 1 by decide,ite_true,ite_false,triangleBlocks,replaceZero]
  simp
  rw [Finset.sum_comm]

lemma weightedStar_replaceZero_norm_le (A : Three → Matrix ι ι ℂ) (B : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (g : Three → ι → ℝ) (v : Three) (a b : BlockSpace ι) :
    ‖rowStar (weightedArray (replaceZero A B) g) v a b‖ ≤ ‖rowStar (weightedArray A g) v a b‖ := by
  apply rowStar_norm_mono _ v a b
  intro w i j
  simp only [weightedArray_norm]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  by_cases hw : w=0
  · subst w
    simpa only [replaceZero,ite_true] using hB i j
  · simp [replaceZero,hw]
end
end TriangularHilbert.MatrixEnergy
end

end OAI

import OAI.Analysis.TriangularHilbert.ZeroStar

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma sqrt_weight_product_le {a b x y d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (Real.sqrt a*Real.sqrt x)*(Real.sqrt b*Real.sqrt y)*(Real.sqrt a*d*Real.sqrt b) ≤ d*a*b*(x+y)/2 := by
  have hxy : Real.sqrt x*Real.sqrt y ≤ (x+y)/2 := by
    nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy,sq_nonneg (Real.sqrt x-Real.sqrt y)]
  calc
    _ = (Real.sqrt a*Real.sqrt a)*(Real.sqrt b*Real.sqrt b)*d*(Real.sqrt x*Real.sqrt y) := by ring
    _ = d*a*b*(Real.sqrt x*Real.sqrt y) := by rw [Real.mul_self_sqrt ha,Real.mul_self_sqrt hb]; ring
    _ ≤ d*a*b*((x+y)/2) := mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by ring

def jumpSlicing (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (i j : ι) : ℝ :=
  2*(∑ m, ‖A 0 i m‖^2*g 1 m)+2*(∑ m, ‖A 0 m j‖^2*g 0 m)+
    (∑ m, ‖A 2 m i‖^2*g 2 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)

lemma energy_replaceZero_jump_zero (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 0)-energy (starGram (weightedArray (replaceZero A C) g) 0)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 i m‖^2*g 1 m)+(∑ m, ‖A 2 m i‖^2*g 2 m)+(∑ m, ‖A 0 m j‖^2*g 0 m)) := by
  have hj := energy_jump_le (rowStar (weightedArray (replaceZero A C) g) 0)
    (rowStar (weightedArray (replaceZero A B) g) 0) (rowStar (weightedArray A g) 0)
    (weightedStar_replaceZero_norm_le A C hC g 0) (weightedStar_replaceZero_norm_le A B hB g 0)
  rw [← rowStar_sub,← weightedArray_sub,replaceZero_sub,weightedArray_replaceZero_zero,jump_sum_zero (weightedArray A g) (fun i j => (Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ))] at hj
  apply hj.trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [rowNorm_weightedStar_zero A g hg,colNorm_weightedStar_zero_one A g hg]
  have hnorm : ‖(Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ)‖ =
      Real.sqrt (g 0 i)*‖B i j-C i j‖*Real.sqrt (g 1 j) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Matrix.sub_apply]
  rw [hnorm]
  have h := sqrt_weight_product_le
    (x := (∑ m, ‖A 0 i m‖^2*g 1 m)+(∑ m, ‖A 2 m i‖^2*g 2 m))
    (y := ∑ m, ‖A 0 m j‖^2*g 0 m) (hg 0 i) (hg 1 j)
    (add_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 1 m)))
      (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 2 m))))
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 0 m))) (norm_nonneg (B i j-C i j))
  linarith

lemma energy_replaceZero_jump_one (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 1)-energy (starGram (weightedArray (replaceZero A C) g) 1)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)+(∑ m, ‖A 0 i m‖^2*g 1 m)) := by
  have hj := energy_jump_le (rowStar (weightedArray (replaceZero A C) g) 1)
    (rowStar (weightedArray (replaceZero A B) g) 1) (rowStar (weightedArray A g) 1)
    (weightedStar_replaceZero_norm_le A C hC g 1) (weightedStar_replaceZero_norm_le A B hB g 1)
  rw [← rowStar_sub,← weightedArray_sub,replaceZero_sub,weightedArray_replaceZero_zero,jump_sum_one (weightedArray A g) (fun i j => (Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ))] at hj
  apply hj.trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [rowNorm_weightedStar_one A g hg,colNorm_weightedStar_one_zero A g hg]
  have hnorm : ‖(Real.sqrt (g 0 i):ℂ)*(B-C) i j*(Real.sqrt (g 1 j):ℂ)‖ =
      Real.sqrt (g 1 j)*‖B i j-C i j‖*Real.sqrt (g 0 i) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Matrix.sub_apply]
    ring
  rw [hnorm]
  have h := sqrt_weight_product_le
    (x := (∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m))
    (y := ∑ m, ‖A 0 i m‖^2*g 1 m) (hg 1 j) (hg 0 i)
    (add_nonneg (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 0 m)))
      (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 2 m))))
    (Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (hg 1 m))) (norm_nonneg (B i j-C i j))
  nlinarith
end
end TriangularHilbert.MatrixEnergy
end

end OAI

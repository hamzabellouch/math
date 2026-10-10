import OAI.Analysis.TriangularHilbert.WeightedStar

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weightedGram_sub (B : Matrix ι ι ℂ) (f g : ι → ℝ) :
    weightedGram B (fun i => f i-g i) = weightedGram B f-weightedGram B g := by
  unfold weightedGram
  have hd : Matrix.diagonal (fun i => ((f i-g i:ℝ):ℂ)) =
      Matrix.diagonal (fun i => (f i:ℂ))-Matrix.diagonal (fun i => (g i:ℂ)) := by
    rw [Matrix.diagonal_sub]
    simp only [Complex.ofReal_sub]
  rw [hd,Matrix.mul_sub,Matrix.sub_mul]

lemma weightedGram_mono (B : Matrix ι ι ℂ) (f g : ι → ℝ) (hfg : ∀ i, f i ≤ g i) :
    weightedGram B f ≤ weightedGram B g := by
  rw [← sub_nonneg,← weightedGram_sub]
  exact (weightedGram_posSemidef B (fun i => sub_nonneg.mpr (hfg i))).nonneg

lemma rowBare_apply_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three)
    (a b : BlockSpace ι) (ha : a.1 ≠ v) : rowBare A g v a b = 0 := by
  simp [rowBare,vertexRoot,Matrix.mul_diagonal,rowStar_apply,ha]

lemma weightedGram_rowBare_congr (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (v : Three) (f f' : BlockSpace ι → ℝ) (he : ∀ i, f (v,i)=f' (v,i)) :
    weightedGram (rowBare A g v) f = weightedGram (rowBare A g v) f' := by
  ext a b
  unfold weightedGram
  conv_lhs => rw [Matrix.mul_apply]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.1 = v
  · obtain ⟨w,i⟩ := k
    change w = v at hk
    subst w
    rw [he i]
  · rw [rowBare_apply_zero A g v k b hk]
    simp

lemma hessianCost_smul_direction {P K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (c : ℝ) :
    hessianCost P (c • K) = c^2*hessianCost P K := by
  exact rootCost_smul_direction (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol c

omit [Fintype ι] in
lemma blockD_real_diagonal (d : Three → ι → ℝ) :
    blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ))) =
      Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2:ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v=w <;> by_cases hi : i=j <;>
    simp [blockD,blocks,Matrix.diagonal,hv,hi,Prod.mk.injEq]

lemma norm_blockD_real_diagonal_le (d : Three → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ v i, |d v i| ≤ C) :
    ‖blockD (fun v => Matrix.diagonal (fun i => (d v i:ℂ)))‖ ≤ C := by
  rw [blockD_real_diagonal,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun a => by simpa using hd a.1 a.2)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

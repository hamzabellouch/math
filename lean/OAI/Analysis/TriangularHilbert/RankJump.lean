import OAI.Analysis.TriangularHilbert.SignedConvolution

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma abs_hsReal_le_sum (X Y : Matrix ι ι ℂ) :
    |hsReal X Y| ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖ := by
  unfold hsReal traceReal
  calc
    _ ≤ ‖(Xᴴ * Y).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j, ∑ i, ‖star (X i j) * Y i j‖ := by
      unfold Matrix.trace
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_star]; rw [Finset.sum_comm]

def segmentMatrix (A B : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  (1-t) • A + t • B

lemma segmentMatrix_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (segmentMatrix A B) (B-A) t := by
  convert! (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const A).add
    ((hasDerivAt_id t).smul_const B) using 1; simp [sub_eq_add_neg,add_comm]

lemma segmentEnergy_hasDerivAt (A B : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (fun s => energy ((segmentMatrix A B s)ᴴ * segmentMatrix A B s))
      (3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)) t := by
  exact (energyGram_hasFDerivAt _).comp_hasDerivAt t (segmentMatrix_hasDerivAt A B t)

omit [Fintype ι] [DecidableEq ι] in
lemma segmentMatrix_norm_entry_le (A B : Matrix ι ι ℂ) (M : ι → ι → ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ M i j) (hB : ∀ i j, ‖B i j‖ ≤ M i j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (i j : ι) :
    ‖segmentMatrix A B t i j‖ ≤ M i j := by
  calc
    _ ≤ ‖((1-t):ℝ) • A i j‖ + ‖t • B i j‖ := norm_add_le _ _
    _ = (1-t)*‖A i j‖+t*‖B i j‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-t)]
    _ ≤ (1-t)*M i j+t*M i j := add_le_add
      (mul_le_mul_of_nonneg_left (hA i j) (by linarith [ht.2]))
      (mul_le_mul_of_nonneg_left (hB i j) ht.1)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma rowNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (i : ι) :
    rowNorm X i ≤ rowNorm Y i := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun j _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

omit [DecidableEq ι] in
lemma colNorm_mono {X Y : Matrix ι ι ℂ} (h : ∀ i j, ‖X i j‖ ≤ ‖Y i j‖) (j : ι) :
    colNorm X j ≤ colNorm Y j := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun i _ => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (h i j))

lemma energy_jump_le (A B M : Matrix ι ι ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ ‖M i j‖) (hB : ∀ i j, ‖B i j‖ ≤ ‖M i j‖) :
    |energy (Bᴴ*B) - energy (Aᴴ*A)| ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
  have hb (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
      ‖3 * hsReal (segmentMatrix A B t * CFC.sqrt ((segmentMatrix A B t)ᴴ * segmentMatrix A B t)) (B-A)‖ ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (abs_hsReal_le_sum _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (entry_gradient_le _ i j).trans
    have he := segmentMatrix_norm_entry_le A B (fun i j => ‖M i j‖) hA hB ⟨ht.1,ht.2.le⟩
    exact mul_le_mul (rowNorm_mono he i) (colNorm_mono he j) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (segmentEnergy_hasDerivAt A B t).hasDerivWithinAt) hb
  simpa [segmentMatrix,Real.norm_eq_abs] using h
end
end TriangularHilbert.MatrixEnergy
end

end OAI

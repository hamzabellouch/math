import OAI.Analysis.Quantum.PPTSquare.ChannelModel
import OAI.Analysis.Quantum.PPTSquare.Compression
import OAI.Analysis.Quantum.PPTSquare.TensorModel
import OAI.Analysis.Quantum.PPTSquare.TensorPositivity
import OAI.Analysis.Quantum.PPTSquare.SymmetricVectors
import OAI.Analysis.Quantum.PPTSquare.QuadraticCriterion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion
variable {n m r : Type} [Fintype n] [Fintype m] [Fintype r]

omit [Fintype n] in
lemma projector_col_sum (A : Matrix n m ℂ) :
    (∑ j, projector (fun i => A i j)) = A*Aᴴ := by
  ext i k
  simp only [Matrix.sum_apply,projector,Matrix.vecMulVec_apply,Pi.star_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply]

lemma separable_rankone {C : Mat (n × m)} [DecidableEq n] [DecidableEq m]
    (hC : Separable C) :
    ∃ (t : ℕ) (x : Fin t × (n × m) → n → ℂ) (y : Fin t × (n × m) → m → ℂ),
      C = ∑ k, projector (product (x k) (y k)) := by
  obtain ⟨t,A,B,hA,hB,rfl⟩ := hC
  let x : Fin t × (n × m) → n → ℂ := fun k i => CFC.sqrt (A k.1) i k.2.1
  let y : Fin t × (n × m) → m → ℂ := fun k i => CFC.sqrt (B k.1) i k.2.2
  refine ⟨t,x,y,?_⟩
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fintype.sum_prod_type,x,y,projector_product]
  have ha : (∑ j, projector (fun i => CFC.sqrt (A k) i j)) = A k :=
    (projector_col_sum _).trans (sqrt_mul_conjTranspose _ (hA k))
  have hb : (∑ j, projector (fun i => CFC.sqrt (B k) i j)) = B k :=
    (projector_col_sum _).trans (sqrt_mul_conjTranspose _ (hB k))
  calc
    A k ⊗ₖ B k = (∑ j, projector (fun i => CFC.sqrt (A k) i j)) ⊗ₖ
        (∑ j, projector (fun i => CFC.sqrt (B k) i j)) := by rw [ha,hb]
    _ = _ := by
      ext ⟨a,c⟩ ⟨b,d⟩
      simp only [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]

omit [Fintype n] in
lemma norm_sq_sum_le_card (s : Finset n) (z : n → ℂ) :
    ‖∑ i ∈ s, z i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖)
  simp only [one_mul,one_pow,Finset.sum_const,mul_one,nsmul_eq_mul] at h
  have hn := norm_sum_le s z
  have hx : 0 ≤ ∑ i ∈ s, ‖z i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [norm_nonneg (∑ i ∈ s, z i)]

lemma norm_sq_sparse_sum [DecidableEq n] (z : n → ℂ) (κ : ℝ)
    (h : ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ κ) :
    ‖∑ i, z i‖^2 ≤ κ * ∑ i, ‖z i‖^2 := by
  let S := Finset.univ.filter (fun i => z i ≠ 0)
  have hsum : ∑ i ∈ S, z i = ∑ i, z i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [S] using hi
  have hsq : ∑ i ∈ S, ‖z i‖^2 = ∑ i, ‖z i‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : z i=0 := by simpa [S] using hi
    simp [hz]
  have hc := norm_sq_sum_le_card S z
  rw [hsum,hsq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

lemma mul_star_re (z : ℂ) : (z * star z).re = ‖z‖^2 := by
  rw [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

omit [Fintype n] in
lemma projector_diagonal (z : n → ℂ) (i : n) : (projector z i i).re = ‖z i‖^2 :=
  mul_star_re _
lemma projector_all_sum (z : n → ℂ) :
    (∑ i, ∑ j, projector z i j).re = ‖∑ i, z i‖^2 := by
  simp only [projector,Matrix.vecMulVec_apply,Pi.star_apply]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← star_sum]
  exact mul_star_re _

def compressionSum (C : Mat (n × n)) : ℝ := (∑ i, ∑ j, C (i,i) (j,j)).re
def compressionTrace (C : Mat (n × n)) : ℝ := (∑ i, C (i,i) (i,i)).re

theorem separable_compression_bound [DecidableEq n] {C : Mat (n × n)}
    (hC : Separable C) (κ : ℝ)
    (hclique : ∀ J : Finset n,
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → 0 < (C (i,j) (i,j)).re) → (J.card : ℝ) ≤ κ) :
    compressionSum C ≤ κ * compressionTrace C := by
  obtain ⟨t,x,y,hC⟩ := separable_rankone hC
  let z := fun k i => x k i * y k i
  have hd (i j : n) : (C (i,j) (i,j)).re = ∑ k, ‖x k i * y k j‖^2 := by
    rw [hC]
    simp only [Matrix.sum_apply,Complex.re_sum,projector_diagonal,product]
  have hsupport (k : Fin t × (n × n)) :
      ((Finset.univ.filter (fun i => z k i ≠ 0)).card : ℝ) ≤ κ := by
    apply hclique
    intro i hi j hj _
    have hi' : x k i ≠ 0 := (mul_ne_zero_iff.mp (Finset.mem_filter.mp hi).2).1
    have hj' : y k j ≠ 0 := (mul_ne_zero_iff.mp (Finset.mem_filter.mp hj).2).2
    rw [hd]
    have hle : ‖x k i*y k j‖^2 ≤ ∑ k', ‖x k' i*y k' j‖^2 :=
      Finset.single_le_sum (fun k' _ => sq_nonneg ‖x k' i*y k' j‖) (Finset.mem_univ k)
    exact (sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hi' hj'))).trans_le hle
  have hs : compressionSum C = ∑ k, ‖∑ i, z k i‖^2 := by
    rw [hC]
    simp only [compressionSum,Matrix.sum_apply,Complex.re_sum]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    have he (i j : n) : projector (product (x k) (y k)) (i,i) (j,j) = projector (z k) i j := rfl
    simp only [he,← Complex.re_sum,projector_all_sum]
  have ht : compressionTrace C = ∑ k, ∑ i, ‖z k i‖^2 := by
    rw [hC]
    simp only [compressionTrace,Matrix.sum_apply,Complex.re_sum,projector_diagonal,product,z]
    rw [Finset.sum_comm]
  rw [hs,ht,Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => norm_sq_sparse_sum (z k) κ (hsupport k))
end ProjectionCriterion

end

end OAI

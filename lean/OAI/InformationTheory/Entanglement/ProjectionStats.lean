import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion
namespace Data
variable {Q K D I : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [DecidableEq Q] [DecidableEq D] [DecidableEq I]
variable (d : Data Q K D I)

lemma adjoint_apply (A : Mat D) (i j : I) :
    hsAdjoint d.Psi A i j = Matrix.trace ((d.H i j)ᴴ * A) := by
  simp only [hsAdjoint,d.Psi_single]
  change (∑ a, ∑ b, star (d.H i j a b)*A a b) =
    ∑ a, ∑ b, star (d.H i j b a)*A b a
  rw [Finset.sum_comm]
lemma C_entry (i j a b : I) : d.C (i,a) (j,b) = Matrix.trace ((d.H a b)ᴴ*d.H i j) := by
  change hsAdjoint d.Psi (d.Psi (Matrix.single i j 1)) a b = _
  rw [d.Psi_single,d.adjoint_apply]
lemma C_diag (i j : I) : d.C (i,j) (i,j) = Matrix.trace (d.P i*d.P j) := by
  rw [d.C_entry,d.H_self,d.H_self,(d.hermitian j).eq,Matrix.trace_mul_comm]
omit [DecidableEq I] in
lemma overlap_gram (i j : I) :
    Matrix.trace ((d.P i*d.P j)ᴴ*(d.P i*d.P j))=Matrix.trace (d.P i*d.P j) := by
  rw [Matrix.conjTranspose_mul,(d.hermitian i).eq,(d.hermitian j).eq]
  calc
    Matrix.trace (d.P j*d.P i*(d.P i*d.P j)) =
        Matrix.trace (d.P j*(d.P i*d.P i)*d.P j) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (d.P j*d.P i*d.P j) := by rw [d.idempotent]
    _ = Matrix.trace (d.P j*d.P j*d.P i) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (d.P i*d.P j) := by rw [d.idempotent,Matrix.trace_mul_comm]
omit [DecidableEq I] in
lemma overlap_nonneg (i j : I) : 0 ≤ (Matrix.trace (d.P i*d.P j)).re := by
  rw [← d.overlap_gram]
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (d.P i*d.P j)).trace_nonneg).1
omit [DecidableEq I] in
lemma overlap_im (i j : I) : (Matrix.trace (d.P i*d.P j)).im=0 := by
  rw [← d.overlap_gram]
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (d.P i*d.P j)).trace_nonneg).2.symm
lemma B_entry (i j : I) : d.B i j = ((d.c i j)^2 : ℂ) * Matrix.trace (d.P i*d.P j) := by
  change d.C (i,i) (j,j) = _
  rw [d.C_entry]
  simp only [H,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul,smul_eq_mul]
  rw [d.overlap_gram]
  ring
omit [DecidableEq I] in
lemma weighted_trace (f : Q → ℂ) (A : Mat D) :
    (∑ i, f (d.question i)*Matrix.trace (A*d.P i)) =
      (∑ q, f q)*Matrix.trace A := by
  rw [← Finset.sum_fiberwise Finset.univ d.question]
  calc
    (∑ q, ∑ i with d.question i=q, f (d.question i)*Matrix.trace (A*d.P i)) =
        ∑ q, f q * Matrix.trace A := by
      apply Finset.sum_congr rfl
      intro q _
      calc
        (∑ i with d.question i=q, f (d.question i)*Matrix.trace (A*d.P i)) =
            ∑ i with d.question i=q, f q*Matrix.trace (A*d.P i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = f q*Matrix.trace (A*(∑ i with d.question i=q, d.P i)) := by
          simp only [Matrix.trace_sum,Finset.mul_sum]
        _ = f q*Matrix.trace A := by rw [d.complete,Matrix.mul_one]
    _ = _ := (Finset.sum_mul ..).symm
omit [DecidableEq I] in
lemma weighted_projector_trace (f : Q → ℂ) :
    (∑ i, f (d.question i)*Matrix.trace (d.P i)) =
      (∑ q, f q)*(Fintype.card D : ℂ) := by
  simpa only [Matrix.one_mul,Matrix.trace_one] using d.weighted_trace f 1
omit [DecidableEq I] in
lemma weighted_overlap (f : Q → Q → ℂ) :
    (∑ i, ∑ j, f (d.question i) (d.question j)*Matrix.trace (d.P i*d.P j)) =
      (∑ q, ∑ r, f q r)*(Fintype.card D : ℂ) := by
  simp_rw [d.weighted_trace]
  exact d.weighted_projector_trace (fun q => ∑ r, f q r)
lemma C_trace : Matrix.trace d.C = (Fintype.card Q : ℂ)^2*(Fintype.card D : ℂ) := by
  change (∑ ij, d.C ij ij) = _
  rw [Fintype.sum_prod_type]
  simp_rw [d.C_diag]
  have h := d.weighted_overlap (fun _ _ => 1)
  simpa only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,pow_two] using h
lemma B_trace : Matrix.trace d.B = (Fintype.card Q : ℂ)*(Fintype.card D : ℂ) := by
  change (∑ i, d.C (i,i) (i,i)) = _
  simp_rw [d.C_diag,d.idempotent]
  have h := d.weighted_projector_trace (fun _ => 1)
  simpa only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h
lemma B_sum : (∑ i, ∑ j, d.B i j) =
    ((∑ q, ∑ r, (correlation d.u q r)^2 : ℝ) : ℂ)*(Fintype.card D : ℂ) := by
  simp only [d.B_entry,c]
  rw [d.weighted_overlap (fun q r => (correlation d.u q r : ℂ)^2)]
  push_cast
  rfl
end Data
end ProjectionCriterion

end

end OAI
